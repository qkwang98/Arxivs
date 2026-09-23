"""Dormand-Prince 5(4) with exact rational coefficients and mpmath stages.

Tableau and RMS step controller follow scipy.integrate.RK45. Requested
output points are hit by steps, without a lower-order dense interpolant.
"""
from bisect import bisect_right
from time import perf_counter

from mpmath import mp

import high_precision as hp


def tableau():
    def rational(s):
        num,den = s.split('/') if '/' in s else (s,'1')
        return mp.mpf(num)/int(den)
    rows = [[], ['1/5'], ['3/40','9/40'],
            ['44/45','-56/15','32/9'],
            ['19372/6561','-25360/2187','64448/6561','-212/729'],
            ['9017/3168','-355/33','46732/5247','49/176','-5103/18656']]
    aa = [[rational(v) for v in row] for row in rows]
    bb = list(map(rational,['35/384','0','500/1113','125/192','-2187/6784','11/84']))
    cc = list(map(rational,['0','1/5','3/10','4/5','8/9','1']))
    ee = list(map(rational,['-71/57600','0','71/16695','-71/1920','17253/339200','-22/525','1/40']))
    return aa,bb,cc,ee


def rk_step(fun,t,y,f,step,coefficients):
    aa,bb,cc,ee = coefficients
    stages = [f]
    for s in range(1,6):
        trial = [y[j]+step*sum(aa[s][k]*stages[k][j] for k in range(s)) for j in range(len(y))]
        stages.append(fun(t+cc[s]*step,trial))
    new = [y[j]+step*sum(bb[k]*stages[k][j] for k in range(6)) for j in range(len(y))]
    stages.append(fun(t+step,new))
    error = [step*sum(ee[k]*stages[k][j] for k in range(7)) for j in range(len(y))]
    return new,stages[-1],error


class SharedPotential:
    """Evaluate only q from the shared background, never its reference F."""
    def __init__(self,reference):
        self.reference = reference
        self.p = reference.p

    def __call__(self,t):
        ref = self.reference
        sign = 1 if t >= 0 else -1
        index = max(0,bisect_right(ref.starts[sign],abs(float(t)))-1)
        origin,end,coeff = ref.segments[sign][index]
        if abs(t) > abs(end)+mp.mpf('1e-12'):
            raise ValueError('Potential requested outside the background interval')
        q = hp.horner(coeff[0],t-origin)
        x = self.p.x0+t
        return x*x-(2*self.p.b-1)+6*x*q+mp.mpf(15)/4*q*q+12*self.p.a*self.p.a/(q*q)


def integrate(fun,points,initial,tolerance,max_step='.2',max_attempts=500000):
    rtol = mp.mpf(tolerance)
    if rtol <= 0 or rtol < 100*mp.eps:
        raise ValueError('Tolerance must be positive and resolved by the working precision')
    atol,cap = rtol/10,mp.mpf(max_step)
    coeff = tableau()
    out = {0.:list(initial)}
    stats = {'accepted_steps':0,'rejected_steps':0,'nfev':0}
    for sign in (-1,1):
        targets = sorted([mp.mpf(float(v)) for v in points if sign*v > 0],key=abs)
        if not targets:
            continue
        t,y = mp.mpf(0),list(initial)
        f = fun(t,y)
        stats['nfev'] += 1
        size = min(mp.mpf('.01'),cap)
        for target in targets:
            while sign*(target-t) > 0:
                if stats['accepted_steps']+stats['rejected_steps'] >= max_attempts:
                    raise RuntimeError('Runge-Kutta attempt budget exceeded')
                rejected = False
                while True:
                    step = sign*min(size,cap,abs(target-t))
                    if t+step == t:
                        raise RuntimeError('Runge-Kutta step underflow')
                    new,fn,error = rk_step(fun,t,y,f,step,coeff)
                    stats['nfev'] += 6
                    norm = mp.sqrt(sum(abs(error[j]/(atol+rtol*max(abs(y[j]),abs(new[j]))))**2
                                       for j in range(len(y)))/len(y))
                    if norm < 1:
                        factor = min(10,mp.mpf('.9')*norm**(-mp.mpf(1)/5)) if norm else mp.mpf(10)
                        if rejected:
                            factor = min(1,factor)
                        size = abs(step)*factor
                        t,y,f = t+step,new,fn
                        stats['accepted_steps'] += 1
                        break
                    size = abs(step)*max(mp.mpf('.2'),mp.mpf('.9')*norm**(-mp.mpf(1)/5))
                    rejected = True
                    stats['rejected_steps'] += 1
                    if stats['accepted_steps']+stats['rejected_steps'] >= max_attempts:
                        raise RuntimeError('Runge-Kutta attempt budget exceeded')
            out[float(target)] = y.copy()
    return out,stats


def fundamental(reference,points,tolerance):
    start = perf_counter()
    potential = SharedPotential(reference)
    def rhs(t,y):
        u = potential(t)
        return [y[1],u*y[0],y[3],u*y[2]]
    values,stats = integrate(rhs,points,[mp.mpc(1),mp.mpc(0),mp.mpc(0),mp.mpc(1)],tolerance)
    matrices = {t:mp.matrix([[v[0],v[2]],[v[1],v[3]]]) for t,v in values.items()}
    stats.update({'seconds':perf_counter()-start,'tolerance':str(tolerance),'digits':mp.dps})
    return matrices,stats
