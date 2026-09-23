"""General-parameter PII Stokes data on the rigid-loss background.

Canonical columns are continued to a nonzero spectral vertex on an explicit
lift. Monodromy sensitivities are computed afresh, without x-transport or
projection. Optional contour solutions use background-only B transport.
"""
from bisect import bisect_right

from mpmath import mp

from high_precision import conv,horner,step_radius
import pii_core as pii


def background_coefficients(t,state,epsilon,order):
    def product(a,b,n):
        return sum(a[k]*b[n-k] for k in range(n+1))
    cf = [[v] for v in state]
    u,p,y1,p1,y2,p2 = cf
    square,potential = [],[]
    for n in range(order):
        square.append(product(u,u,n))
        potential.append(6*square[n]+(t if n == 0 else 1 if n == 1 else 0))
        rhs = [p[n], (1 if n == 0 else 0)-2*product(square,u,n)-t*u[n]-(u[n-1] if n else 0),
               p1[n],-product(potential,y1,n),p2[n],-product(potential,y2,n)]
        for seq,v in zip(cf,rhs):
            seq.append(v/(epsilon*(n+1)))
    return cf


class Reference:
    def __init__(self,epsilon='.2',end='-1',digits=90,tolerance='1e-36',order=40):
        self.digits,self.order = digits,order
        self.segments = []
        with mp.workdps(digits):
            self.epsilon,self.t0,self.end = mp.mpf(epsilon),mp.mpf(-7),mp.mpf(end)
            eps,t0 = self.epsilon,self.t0
            r = mp.findroot(lambda u:2*u**3+t0*u-1,(-2,-1.7))
            k = 6*r*r+t0
            rp = -r/k
            kp = 12*r*rp+1
            correction = 12*r**3/k**4-2*r/k**3
            derivative = 36*r*r*rp/k**4-48*r**3*kp/k**5-2*rp/k**3+6*r*kp/k**4
            self.initial = [r+eps**2*correction,eps*(rp+eps**2*derivative),mp.mpf(1),mp.mpf(0),mp.mpf(0),mp.mpf(1)]
            t,state = t0,self.initial
            while t < self.end:
                cf = background_coefficients(t,state,eps,order)
                size = min(step_radius(cf,mp.mpf(tolerance),'.1'),self.end-t)
                if size < mp.mpf('1e-15'):
                    raise RuntimeError('Rigid PII background step below floor')
                self.segments.append((t,t+size,cf))
                state = [horner(seq,size) for seq in cf]
                t += size
        self.starts = [a for a,_,_ in self.segments]

    def at(self,t):
        with mp.workdps(self.digits):
            t = mp.mpf(t)
            if t < self.t0 or t > self.end:
                raise ValueError('Point outside background interval')
            k = max(0,bisect_right(self.starts,t)-1)
            origin,_,cf = self.segments[k]
            return [horner(seq,t-origin) for seq in cf]

    def matrix(self,t):
        state = self.at(t)
        return mp.matrix([[state[2],state[4]],[state[3],state[5]]])

    def potential(self,t):
        k = max(0,bisect_right(self.starts,t)-1)
        origin,_,cf = self.segments[k]
        u = horner(cf[0],t-origin)
        return 6*u*u+t

    def standard(self,t):
        u,p = self.at(t)[:2]
        r = self.epsilon**(mp.mpf(1)/3)
        return -t/(r*r),mp.j*u/r,-mp.j*p/(r*r),mp.j/self.epsilon

    def peak(self,guess):
        return mp.findroot(lambda t:self.at(t)[1],(mp.mpf(guess)-self.epsilon/4,mp.mpf(guess)+self.epsilon/4))


def formal_column(x,q,w,alpha,sign,order):
    ii = sign*mp.j
    r = [mp.mpc(0),ii*q/2,w/4]
    for m in range(1,order+1):
        lhs = -(m-1)*r[m-1] if m >= 2 else 0
        square_next = sum(r[k]*r[m+1-k] for k in range(1,m+1))
        square = sum(r[k]*r[m-k] for k in range(1,m))
        square_prev = sum(r[k]*r[m-1-k] for k in range(1,m-1))
        rhs = lhs-ii*(2*x+4*q*q)*r[m]+4*q*square_next+2*ii*w*square
        rhs += (alpha if m == 1 else 0)-alpha*square_prev
        r.append(rhs/(8*ii))
    log_amp = [mp.mpc(0)]
    for n in range(1,order+1):
        log_amp.append(-(4*q*r[n+2]+2*ii*w*r[n+1]-alpha*r[n])/n)
    amp = [mp.mpc(1)]
    for n in range(1,order+1):
        amp.append(sum(k*log_amp[k]*amp[n-k] for k in range(1,n+1))/n)
    other = [conv(r,amp,n) for n in range(order+1)]
    return [amp,other] if sign == 1 else [other,amp]


def spectral_coefficients(z,state,x,q,w,alpha,order,sensitivity):
    cf = [[v] for v in state]
    divided = [[] for _ in state]
    groups = 3 if sensitivity else 1
    diagonal = -mp.j*(4*z*z+x+2*q*q)
    upper,lower = 4*q*z+2*mp.j*w,4*q*z-2*mp.j*w
    for n in range(order):
        for j in range(len(state)):
            divided[j].append((cf[j][n]-(divided[j][n-1] if n else 0))/z)
        for g in range(groups):
            j = 2*g
            a,b = cf[j:j+2]
            ra = diagonal*a[n]+upper*b[n]-alpha*divided[j+1][n]
            rb = lower*a[n]-diagonal*b[n]-alpha*divided[j][n]
            if n:
                ra += -8*mp.j*z*a[n-1]+4*q*b[n-1]
                rb += 4*q*a[n-1]+8*mp.j*z*b[n-1]
            if n >= 2:
                ra -= 4*mp.j*a[n-2]
                rb += 4*mp.j*b[n-2]
            if g == 1:
                ra += -4*mp.j*q*cf[0][n]+4*z*cf[1][n]
                rb += 4*z*cf[0][n]+4*mp.j*q*cf[1][n]
                if n:
                    ra += 4*cf[1][n-1]
                    rb += 4*cf[0][n-1]
            elif g == 2:
                ra += 2*mp.j*cf[1][n]
                rb -= 2*mp.j*cf[0][n]
            a.append(ra/(n+1))
            b.append(rb/(n+1))
    return cf


def vertices(index,radius,vertex):
    angle = -mp.pi/6+index*mp.pi/3
    path = [radius*mp.exp(mp.j*angle),vertex*mp.exp(mp.j*angle)]
    pieces = max(1,int(mp.ceil(abs(angle)/(mp.pi/6))))
    path.extend(vertex*mp.exp(mp.j*angle*(1-mp.mpf(k)/pieces)) for k in range(1,pieces+1))
    return path


def canonical(x,q,w,alpha,index,radius=8,formal_order=80,tolerance='1e-32',
              vertex='1.5',order=40,sensitivity=False,quadrature=False):
    radius,vertex,tol = mp.mpf(radius),mp.mpf(vertex),mp.mpf(tolerance)
    path = vertices(index,radius,vertex)
    z0 = path[0]
    sign = 1 if index % 2 == 0 else -1
    def initial(qq,ww):
        return [horner(cf,1/z0) for cf in formal_column(x,qq,ww,alpha,sign,formal_order)]
    state = initial(q,w)
    boundary = -mp.j*(state[0]**2-state[1]**2)/2
    if sensitivity:
        delta = mp.power(10,-mp.dps//3)
        for dq,dw in ((delta,0),(0,delta)):
            plus,minus = initial(q+dq,w+dw),initial(q-dq,w-dw)
            state.extend((a-b)/(2*delta) for a,b in zip(plus,minus))
    integrals = [mp.mpc(0),mp.mpc(0)]
    steps = 0
    for start,end in zip(path[:-1],path[1:]):
        z = start
        while abs(end-z)>mp.mpf('1e-70'):
            cf = spectral_coefficients(z,state,x,q,w,alpha,order,sensitivity)
            kernel = pii.kernel_coefficients(z,cf,q) if quadrature else None
            controlled = cf if kernel is None else cf+[[integrals[k]]+[v/(n+1) for n,v in enumerate(seq)]
                                                       for k,seq in enumerate(kernel)]
            size = min(step_radius(controlled,tol,min(mp.mpf('.4'),abs(z)/4)),abs(end-z))
            step = (end-z)/abs(end-z)*size
            if quadrature:
                for k,seq in enumerate(kernel):
                    integrals[k] += step*horner([v/(n+1) for n,v in enumerate(seq)],step)
            state = [horner(seq,step) for seq in cf]
            z += step
            steps += 1
            if steps > 40000:
                raise RuntimeError('General PII spectral step budget exceeded')
    exponent = mp.exp(-sign*mp.j*(4*z0**3/3+x*z0))
    return {'column':mp.matrix([v*exponent for v in state[:2]]),
            'sensitivities':[mp.matrix([v*exponent for v in state[k:k+2]]) for k in (2,4)] if sensitivity else [],
            'integral':mp.matrix([v*exponent**2 for v in integrals]),
            'boundary':boundary*exponent**2,'steps':steps}


def monodromy(reference,t,**settings):
    x,q,w,alpha = reference.standard(t)
    data = [canonical(x,q,w,alpha,j,sensitivity=True,**settings) for j in range(6)]
    values,jac = mp.zeros(4,1),mp.zeros(4,2)
    determinants = []
    for j in range(4):
        a,b,c = [data[k]['column'] for k in (j,j+1,j+2)]
        num,den = pii.wedge(a,c),pii.wedge(a,b)
        values[j] = num/den
        determinants.append(den)
        for k in range(2):
            da,db,dc = [data[l]['sensitivities'][k] for l in (j,j+1,j+2)]
            dn = pii.wedge(da,c)+pii.wedge(a,dc)
            dd = pii.wedge(da,b)+pii.wedge(a,db)
            jac[j,k] = (dn*den-num*dd)/den**2
    rho = reference.epsilon**(mp.mpf(1)/3)
    jac = jac*mp.diag([mp.j/rho,-mp.j/(rho*rho)])
    return values,jac,{'adjacent_determinants':determinants,
                       'adjacent_error':max(abs(v-(-1)**j) for j,v in enumerate(determinants)),
                       'spectral_steps':sum(v['steps'] for v in data)}


class Anchor:
    def __init__(self,reference,vertex):
        self.reference,self.vertex = reference,mp.mpf(vertex)
        self.segments = []
        state = [mp.mpc(1),mp.mpc(0),mp.mpc(0),mp.mpc(1)]
        diagonal = mp.j*self.vertex/reference.epsilon**(mp.mpf(2)/3)
        for start,end,background in reference.segments:
            cf = [[v] for v in state]
            u = background[0]
            for n in range(reference.order):
                for j in (0,2):
                    top = diagonal*cf[j][n]-mp.j*conv(u,cf[j+1],n)/reference.epsilon
                    bottom = -mp.j*conv(u,cf[j],n)/reference.epsilon-diagonal*cf[j+1][n]
                    cf[j].append(top/(n+1))
                    cf[j+1].append(bottom/(n+1))
            self.segments.append((start,end,cf))
            state = [horner(seq,end-start) for seq in cf]

    def at(self,t):
        k = max(0,bisect_right(self.reference.starts,t)-1)
        origin,_,cf = self.segments[k]
        v = [horner(seq,t-origin) for seq in cf]
        return mp.matrix([[v[0],v[2]],[v[1],v[3]]])


class Contours:
    groups = [(0,1,2,3),(2,3,4,5)]

    def __init__(self,reference,**settings):
        self.reference,self.settings = reference,settings
        self.anchor = Anchor(reference,settings.get('vertex','1.5'))
        rho = reference.epsilon**(mp.mpf(1)/3)
        self.conversion = mp.diag([-mp.j*rho,mp.j*rho*rho])
        self.base = self.columns(reference.t0)
        self.weights = [pii.cycle_coefficients([self.base[j]['column'] for j in group]) for group in self.groups]
        self.initial,self.initial_boundary = self.assemble(self.base)
        self.inverse = self.initial**-1

    def columns(self,t):
        x,q,w,alpha = self.reference.standard(t)
        return [canonical(x,q,w,alpha,j,quadrature=True,**self.settings) for j in range(6)]

    def assemble(self,data):
        f,boundary = mp.zeros(2),mp.zeros(1,2)
        for k,(group,weights) in enumerate(zip(self.groups,self.weights)):
            for j,c in zip(group,weights):
                for row in range(2):
                    f[row,k] += c*data[j]['integral'][row]
                boundary[k] -= c*data[j]['boundary']
        return self.conversion*f,boundary

    def at(self,t):
        data = self.base if t == self.reference.t0 else self.columns(t)
        transport = self.anchor.at(t)
        fixed = []
        direction,amplitude = mp.mpf(0),mp.mpf(0)
        for j,local in enumerate(data):
            target = transport*self.base[j]['column']
            pivot = max(range(2),key=lambda k:abs(local['column'][k]))
            gamma = target[pivot]/local['column'][pivot]
            direction = max(direction,max(map(abs,gamma*local['column']-target))/max(map(abs,target)))
            amplitude = max(amplitude,abs(gamma-1))
            fixed.append(dict(local,column=gamma*local['column'],integral=gamma**2*local['integral'],boundary=gamma**2*local['boundary']))
        raw,boundary = self.assemble(fixed)
        inner = mp.mpf(0)
        for group,weights in zip(self.groups,self.weights):
            residual = sum((c*pii.squared(fixed[j]['column']) for j,c in zip(group,weights)),mp.zeros(3,1))
            scale = sum(abs(c)*max(map(abs,pii.squared(fixed[j]['column']))) for j,c in zip(group,weights))
            inner = max(inner,max(map(abs,residual))/scale)
        return raw*self.inverse,{'direction_error':direction,'amplitude_correction':amplitude,
                                 'inner_boundary_error':inner,'outer_boundary':max(map(abs,boundary*self.inverse)),
                                 'anchor_unitarity_error':max(map(abs,transport.H*transport-mp.eye(2)))}
