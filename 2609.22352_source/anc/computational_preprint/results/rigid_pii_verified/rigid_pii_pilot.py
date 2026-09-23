#!/usr/bin/env python3
"""Local amplification through the first pulse in Kiselev's 1999 PII model.

This is a background/tangent diagnostic, not a contour-versus-RK comparison.
The independent variable and momentum are the original t and p=epsilon*u_t.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from time import perf_counter

import numpy as np
from scipy.integrate import solve_ivp
import sympy as s


ROOT = Path(__file__).resolve().parent
SOURCE = Path('<arXiv:solv-int/9902007v1.pdf>')
A_STAR = -2.**(-2/3)
T_STAR = -6*A_STAR*A_STAR


def symbolic_checks():
    a,theta,z,x,q,p,alpha = s.symbols('a theta z x q p alpha',nonzero=True)
    k = 4*a*a
    w = -4*a/(1+k*theta**2)
    potential = 12*a*w+6*w*w
    y1 = theta/(1+k*theta**2)**2
    y2 = (-1+4*k*theta**2+2*k*k*theta**4+s.Rational(4,5)*k**3*theta**6
          +s.Rational(1,7)*k**4*theta**8)/(1+k*theta**2)**2
    checks = {'pulse':s.factor(s.diff(w,theta,2)+6*a*w*w+2*w**3),
              'mode1':s.factor(s.diff(y1,theta,2)+potential*y1),
              'mode2':s.factor(s.diff(y2,theta,2)+potential*y2),
              'wronskian_minus_one':s.factor(y1*s.diff(y2,theta)-s.diff(y1,theta)*y2-1)}
    A = s.Matrix([[-s.I*(4*z*z+x+2*q*q),4*q*z-alpha/z+2*s.I*p],
                  [4*q*z-alpha/z-2*s.I*p,s.I*(4*z*z+x+2*q*q)]])
    B = s.Matrix([[-s.I*z,q],[q,s.I*z]])
    curvature = A.diff(x)+A.diff(q)*p+A.diff(p)*(2*q**3+x*q+alpha)-B.diff(z)+A*B-B*A
    checks['general_parameter_zero_curvature'] = s.simplify(curvature)
    c,d = s.symbols('c d')
    cx,dx = B*s.Matrix([c,d])
    cz,dz = A*s.Matrix([c,d])
    def derivative_x(f):
        return s.diff(f,x)+s.diff(f,q)*p+s.diff(f,p)*(2*q**3+x*q+alpha)+s.diff(f,c)*cx+s.diff(f,d)*dx
    K, R = c*c+d*d,-s.I*(c*c-d*d)/2
    Rz = s.diff(R,z)+s.diff(R,c)*cz+s.diff(R,d)*dz
    checks['general_parameter_kernel'] = s.expand(derivative_x(derivative_x(K))-(6*q*q+x)*K-Rz)
    rho,qxx = s.symbols('rho qxx',positive=True)
    uq = -s.I*rho*q
    original = -s.I*rho**3*qxx+2*uq**3-rho*rho*x*uq-1
    checks['standard_scaling'] = s.expand(original+s.I*rho**3*(qxx-2*q**3-x*q-s.I/rho**3))
    delta,tau,V,Vpp,Z,Zpp = s.symbols('delta tau V Vpp Z Zpp')
    original_inner = delta**2*Vpp+2*(a+delta*V)**3+(-6*a*a+delta**2*tau)*(a+delta*V)-1
    reduced_inner = delta**2*(Vpp+6*a*V*V+a*tau+delta*(2*V**3+tau*V))
    checks['inner_scaling_at_fold'] = s.expand(original_inner-reduced_inner+4*a**3+1)
    linear_inner = delta*Zpp+(6*(a+delta*V)**2-6*a*a+delta**2*tau)*Z
    checks['linear_inner_scaling'] = s.expand(linear_inner-delta*(Zpp+12*a*V*Z+delta*(6*V*V+tau)*Z))
    printed = (-s.Rational(1,8)+2*a*a*theta**2-a*theta**4+s.Rational(2,5)*theta**6
               +s.Rational(2,7)*theta**8)/(1+k*theta**2)**2
    astar = -2**(-s.Rational(2,3))
    correction = 2*(a*a-1)*theta**8/(7*(1+k*theta**2)**2)
    checks['printed_mode_correction'] = s.simplify((y2/8-printed-correction).subs(a,astar))
    printed_residual = (s.diff(printed,theta,2)+potential*printed).subs({a:astar,theta:1})
    for name,value in checks.items():
        if value != 0 and value != s.zeros(2):
            raise AssertionError((name,value))
    return {'identities':{name:str(value) for name,value in checks.items()},
            'printed_second_mode_residual_at_theta1':float(printed_residual),
            'PI_indicial_exponents':[-3,4]}


def initial_state(epsilon,t0=-7.):
    roots = np.roots([2.,0.,t0,-1.])
    root = min(v.real for v in roots if abs(v.imag)<1e-12)
    k = 6*root*root+t0
    rp = -root/k
    kp = 12*root*rp+1
    correction = 12*root**3/k**4-2*root/k**3
    derivative = 36*root*root*rp/k**4-48*root**3*kp/k**5-2*rp/k**3+6*root*kp/k**4
    u = root+epsilon**2*correction
    up = rp+epsilon**2*derivative
    return np.array([u,epsilon*up,1.,0.,0.,1.])


def run(epsilon,tolerance=1e-11):
    start = perf_counter()
    t0 = -7.
    initial = initial_state(epsilon,t0)
    def rhs(t,y):
        u,p = y[:2]
        k = 6*u*u+t
        return np.array([p,1-2*u**3-t*u,y[3],-k*y[2],y[5],-k*y[4]])/epsilon
    def peak(t,y):
        return y[1]
    peak.direction,peak.terminal = -1,True
    options = dict(method='DOP853',rtol=tolerance,atol=tolerance/100,dense_output=True)
    before = solve_ivp(rhs,(t0,2.),initial,events=peak,**options)
    if not before.success or not before.t_events[0].size:
        raise RuntimeError('First pulse maximum was not reached')
    tpeak = before.t_events[0][0]
    if tpeak <= T_STAR:
        raise RuntimeError('Detected an oscillation before the fold, not the first pulse')
    after = solve_ivp(rhs,(tpeak,tpeak+2*epsilon),before.y_events[0][0],**options)
    if not after.success:
        raise RuntimeError(after.message)
    offsets = np.linspace(-2,2,401)
    times = tpeak+epsilon*offsets
    states = np.array([before.sol(t) if t <= tpeak else after.sol(t) for t in times])
    f = states[:,2:].reshape(-1,2,2).transpose(0,2,1)
    k0 = 6*initial[0]**2+t0
    # This fixed determinant-one input scaling gives equal WKB phase weights.
    balanced = f@np.diag([k0**(-.25),k0**.25])
    gain = np.linalg.svd(f,compute_uv=False)[:,0]
    bgain = np.linalg.svd(balanced,compute_uv=False)[:,0]
    theta = offsets
    profile = A_STAR-4*A_STAR/(1+4*A_STAR*A_STAR*theta*theta)
    return {'epsilon':epsilon,'tolerance':tolerance,'t0':t0,'initial':initial.tolist(),
            'first_peak_t':tpeak,'inner_peak_tau':(tpeak-T_STAR)/epsilon**.8,
            'first_peak_u':float(before.y_events[0][0][0]),
            'max_gain_scaled_physical_state':float(gain.max()),
            'max_gain_balanced_input':float(bgain.max()),
            'gain_times_epsilon_to_7_over_10':float(bgain.max()*epsilon**.7),
            'max_determinant_error':float(np.max(np.abs(np.linalg.det(f)-1))),
            'pulse_profile_error_on_window':float(np.max(np.abs(states[:,0]-profile))),
            'nfev':before.nfev+after.nfev,'seconds':perf_counter()-start,
            'offsets':offsets.tolist(),'u':states[:,0].tolist(),
            'gain':gain.tolist(),'balanced_gain':bgain.tolist()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=ROOT/'results/rigid_pii')
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    shutil.copy2(Path(__file__),args.output/Path(__file__).name)
    digest = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    data = {'status':'running','source_pdf_sha256':digest,'a_star':A_STAR,'t_star':T_STAR,
            'symbolic':symbolic_checks(),'runs':[],
            'scope':'DOP853 background/tangent pilot only; no monodromy or contour calculation.',
            'linear_state':'(delta u, epsilon*delta u_t); F(t0)=I; balanced input diag(k0^-1/4,k0^1/4)',
            'prediction':'Formal matched-asymptotic prediction: balanced first-pulse gain O(epsilon^-7/10).'}
    def save():
        (args.output/'results.json').write_text(json.dumps(data,indent=2)+'\n')
    for eps in (.2,.1,.05,.02,.01,.005):
        record = run(eps)
        data['runs'].append(record)
        print(json.dumps({key:value for key,value in record.items()
                          if key not in ('offsets','u','gain','balanced_gain')}),flush=True)
        save()
    data['refinements'] = {}
    for epsilon in (.02,.005):
        fine = run(epsilon,5e-13)
        coarse = next(v for v in data['runs'] if v['epsilon']==epsilon)
        data['refinements'][str(epsilon)] = {
            'relative_gain_change':abs(fine['max_gain_balanced_input']/coarse['max_gain_balanced_input']-1),
            'peak_time_change':abs(fine['first_peak_t']-coarse['first_peak_t']),
            'max_determinant_error':fine['max_determinant_error']}
    selected = data['runs'][-3:]
    data['loglog_slope_last_three'] = float(np.polyfit(np.log([v['epsilon'] for v in selected]),
                                                     np.log([v['max_gain_balanced_input'] for v in selected]),1)[0])
    data['source_unchanged'] = hashlib.sha256(SOURCE.read_bytes()).hexdigest()==digest
    data['status'] = 'complete'
    save()
    print('Slope:',data['loglog_slope_last_three'],flush=True)
    print('Refinement:',data['refinements'],flush=True)


if __name__ == '__main__':
    main()
