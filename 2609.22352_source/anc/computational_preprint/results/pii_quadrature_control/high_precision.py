"""Multiple-precision Taylor continuation and local canonical Lax columns.

All Taylor coefficients come from algebraic recurrences, not numerical
differentiation. Error controls are refinement diagnostics, not enclosures.
"""
from bisect import bisect_right

import mpmath as mpm
from mpmath import mp
import numpy as np

import compare_monodromy as c


def mc(z):
    return mp.mpc(float(z.real), float(z.imag))


class Parameters:
    def __init__(self):
        # Embed the pilot's binary initial data exactly; do not silently change
        # them to decimal data while investigating sensitive continuation.
        self.x0, self.q0, self.h0 = map(mc, (c.core.X0, c.core.Q0, c.core.H0))
        self.a, self.b = map(mc, (c.core.THETA0, c.core.THETAINF))


def conv(a, b, n):
    return sum((a[k]*b[n-k] for k in range(n+1)), mp.mpc(0))


def horner(coeff, step):
    value = coeff[-1]
    for term in reversed(coeff[:-1]):
        value = value*step+term
    return value


def step_radius(coefficients, tol, cap):
    order = len(coefficients[0])-1
    radius = mp.mpf(cap)
    for series in coefficients:
        scale = max(1, abs(series[0]))
        for n in range(order-2, order+1):
            if series[n]:
                radius = min(radius, (tol*scale/abs(series[n]))**(mp.mpf(1)/n))
    return radius*mp.mpf('.7')


def reference_coefficients(x, state, p, order):
    series = [[v] for v in state]
    q, h, r, logq, logd, y1, v1, y2, v2 = series
    potential = []
    for n in range(order):
        qh, qq, hh, rr = (conv(a, b, n) for a, b in ((q,h),(q,q),(h,h),(r,r)))
        xq = x*q[n]+(q[n-1] if n else 0)
        xh = x*h[n]+(h[n-1] if n else 0)
        xr = x*r[n]+(r[n-1] if n else 0)
        xx = x*x if n == 0 else 2*x if n == 1 else 1 if n == 2 else 0
        potential.append(xx-(2*p.b-1 if n == 0 else 0)+6*xq+mp.mpf(15)/4*qq+12*p.a*p.a*rr)
        rhs = [2*qh+qq+2*xq,
               -hh-2*qh-2*xh-(2*p.b if n == 0 else 0)-4*p.a*p.a*rr,
               -2*conv(r,h,n)-conv(r,q,n)-2*xr,
               2*h[n]+q[n]+(2*x if n == 0 else 2 if n == 1 else 0),
               q[n]/2+(x if n == 0 else 1 if n == 1 else 0),
               v1[n], conv(potential,y1,n), v2[n], conv(potential,y2,n)]
        for seq, value in zip(series, rhs):
            seq.append(value/(n+1))
    return series


class TaylorReference:
    def __init__(self, span=6, digits=50, tolerance='1e-28', order=32):
        self.digits, self.order = digits, order
        self.segments, self.cost = {}, {}
        with mp.workdps(digits):
            self.p = Parameters()
            p = self.p
            initial = [p.q0, p.h0, 1/p.q0, mp.log(p.q0), mp.mpc(0),
                       mp.mpc(1), mp.mpc(0), mp.mpc(0), mp.mpc(1)]
            self.initial = initial
            for sign in (-1, 1):
                t, state, segments = mp.mpf(0), initial, []
                while abs(t) < span:
                    coeff = reference_coefficients(p.x0+t, state, p, order)
                    size = min(step_radius(coeff, mp.mpf(tolerance), '.2'), span-abs(t))
                    if size < mp.mpf('1e-12'):
                        raise RuntimeError('Reference step below 1e-12')
                    step = sign*size
                    segments.append((t, t+step, coeff))
                    state = [horner(seq, step) for seq in coeff]
                    t += step
                self.segments[sign] = segments
                self.cost[sign] = len(segments)
        self.starts = {sgn: [float(abs(a)) for a, _, _ in seq]
                       for sgn, seq in self.segments.items()}
        self.qdouble = {sgn: [np.array([complex(v) for v in cf[0]]) for _, _, cf in seq]
                        for sgn, seq in self.segments.items()}

    def at(self, t):
        with mp.workdps(self.digits):
            sign = 1 if t >= 0 else -1
            index = max(0, bisect_right(self.starts[sign], abs(float(t)))-1)
            origin, end, coeff = self.segments[sign][index]
            if abs(t) > abs(end)+mp.mpf('1e-12'):
                raise ValueError('Requested point outside reference interval')
            return [horner(seq, mp.mpf(t)-origin) for seq in coeff]

    def matrix(self, t):
        s = self.at(t)
        return mp.matrix([[s[5],s[7]],[s[6],s[8]]])

    def q_float(self, t):
        sign = 1 if t >= 0 else -1
        index = max(0, bisect_right(self.starts[sign], abs(float(t)))-1)
        origin = float(self.segments[sign][index][0])
        return np.polynomial.polynomial.polyval(t-origin, self.qdouble[sign][index])


def lax_parts(x, q, h, p):
    chi = q*h+2*p.b
    a0 = mp.matrix([[x,1],[-chi,-x]])
    residue = mp.matrix([[q*h/2,-q/2],[(q*h*h-4*p.a*p.a/q)/2,-q*h/2]])
    return a0, residue


def formal_series(x, q, h, p, order):
    _, d = lax_parts(x,q,h,p)
    chi = q*h+2*p.b
    out = [mp.eye(2)]
    b, cc = -mp.mpf(1)/2, -chi/2
    for n in range(1,order+1):
        prev = out[-1]
        dp = d*prev
        a = ((x+q/2)*cc-((n-1+p.b)*prev[1,0]+dp[1,0])/2)/n
        dd = -(chi*((n-1-p.b)*prev[0,1]+dp[0,1]+2*x*b)/2+d[1,0]*b)/n
        out.append(mp.matrix([[a,b],[cc,dd]]))
        b, cc = -((n-1-p.b)*prev[0,1]+dp[0,1]+2*x*b+dd)/2, ((n-1+p.b)*prev[1,0]+dp[1,0]-2*x*cc-chi*a)/2
    return out


def formal_value(z, series):
    result = series[-1].copy()
    for coefficient in reversed(series[:-1]):
        result = result/z+coefficient
    return result


def spectral_coefficients(z, state, x, q, h, p, order, sensitivity):
    a0, d = lax_parts(x,q,h,p)
    za = a0+mp.matrix([[z,0],[0,-z]])
    aq = mp.matrix([[0,0],[-h,0]])
    ah = mp.matrix([[0,0],[-q,0]])
    dq = mp.matrix([[h/2,-mp.mpf(1)/2],[h*h/2+2*p.a*p.a/q**2,-h/2]])
    dh = mp.matrix([[q/2,0],[q*h,-q/2]])
    groups = 3 if sensitivity else 1
    coeff = [[v] for v in state]
    divided = [[] for _ in state]
    for n in range(order):
        for j in range(len(state)):
            divided[j].append((coeff[j][n]-(divided[j][n-1] if n else 0))/z)
        for g in range(groups):
            off = 2*g
            u = mp.matrix([coeff[off][n],coeff[off+1][n]])
            v = mp.matrix([divided[off][n],divided[off+1][n]])
            rhs = za*u+d*v
            if n:
                rhs += mp.matrix([coeff[off][n-1],-coeff[off+1][n-1]])
            if g:
                base = mp.matrix([coeff[0][n],coeff[1][n]])
                divbase = mp.matrix([divided[0][n],divided[1][n]])
                rhs += (aq if g == 1 else ah)*base+(dq if g == 1 else dh)*divbase
            coeff[off].append(rhs[0]/(n+1))
            coeff[off+1].append(rhs[1]/(n+1))
    return coeff


def kernel_coefficients(z, coeff, x, q, h, root, p):
    u, v = coeff[:2]
    nterms = len(u)-1
    chi, bdiag = q*h+2*p.b, z+x+q/2
    w1 = [bdiag*u[n]+(u[n-1] if n else 0)+v[n] for n in range(nterms)]
    w2 = [-chi*u[n]-bdiag*v[n]-(v[n-1] if n else 0) for n in range(nterms)]
    qp = q*(2*h+q+2*x)
    hp = -h*h-2*h*(q+x)-2*p.b-4*p.a*p.a/q**2
    aa, uw, out, dxout = [], [], [], []
    for n in range(nterms):
        aa.append(conv(u,u,n))
        uw.append(conv(u,w1,n))
        bracket = (h-z)*aa[n]-(aa[n-1] if n else 0)-conv(u,v,n)
        derivative = (qp/(2*q)*bracket+hp*aa[n]+2*(h-z)*uw[n]
                      -2*(uw[n-1] if n else 0)-conv(w1,v,n)-conv(u,w2,n))
        out.append((root*bracket/2-(out[n-1] if n else 0))/z)
        dxout.append((root*derivative/2-(dxout[n-1] if n else 0))/z)
    return out, dxout


def spectral_path(state, vertices, x, q, h, p, tol, order=32, sensitivity=False, root=None):
    integrals = [mp.mpc(0),mp.mpc(0)]
    steps = 0
    for start, end in zip(vertices[:-1],vertices[1:]):
        z = start
        while abs(end-z) > mp.mpf('1e-60'):
            coeff = spectral_coefficients(z,state,x,q,h,p,order,sensitivity)
            size = min(step_radius(coeff,tol,min(mp.mpf('.7'),abs(z)/3)),abs(end-z))
            step = (end-z)/abs(end-z)*size
            if root is not None:
                for k, seq in enumerate(kernel_coefficients(z,coeff,x,q,h,root,p)):
                    integrals[k] += step*horner([v/(n+1) for n,v in enumerate(seq)],step)
            state = [horner(seq,step) for seq in coeff]
            z += step
            steps += 1
            if steps > 30000:
                raise RuntimeError('Spectral path exceeded step budget')
    return state, integrals


def vertices(radius,index,vertex_angle=0):
    angle = index*mp.pi/2
    inner = mp.mpf('1.45')
    path = [radius*mp.exp(1j*angle),inner*mp.exp(1j*angle)]
    pieces = int(mp.ceil(abs(angle-vertex_angle)/(mp.pi/4)))
    if pieces:
        path.extend(inner*mp.exp(1j*(angle+(vertex_angle-angle)*j/pieces)) for j in range(1,pieces+1))
    return path


def canonical_column(x,q,h,p,index,radius,formal_order,tol,*,sensitivity=False,root=None,vertex_angle=0):
    path = vertices(radius,index,vertex_angle)
    z = path[0]
    column = 0 if index % 2 else 1
    sign = 1 if column == 0 else -1
    formal = formal_value(z,formal_series(x,q,h,p,formal_order))
    initial = [formal[0,column],formal[1,column]]
    if sensitivity:
        # A high-precision central difference is used only on the explicit
        # formal coefficients; the spectral sensitivities obey differentiated ODEs.
        eps = mp.power(10,-mp.dps//3)
        for dq,dh in ((eps,0),(0,eps)):
            plus = formal_value(z,formal_series(x,q+dq,h+dh,p,formal_order))
            minus = formal_value(z,formal_series(x,q-dq,h-dh,p,formal_order))
            initial += [(plus[j,column]-minus[j,column])/(2*eps) for j in range(2)]
    result, pair = spectral_path(initial,path,x,q,h,p,tol,sensitivity=sensitivity,root=root)
    theta = z*z/2+x*z-p.b*(mp.log(radius)+1j*index*mp.pi/2)
    factor = mp.exp(sign*theta)
    return [v*factor for v in result], [v*factor**2 for v in pair]


def monodromy(x,q,h,p,radius=16,formal_order=48,tol='1e-30'):
    columns = {}
    for j in range(-4,2):
        values,_ = canonical_column(x,q,h,p,j,mp.mpf(radius),formal_order,mp.mpf(tol),sensitivity=True)
        columns[j] = mp.matrix([[values[0],values[2],values[4]],[values[1],values[3],values[5]]])
    def det(u,v):
        return u[0]*v[1]-u[1]*v[0]
    for index,left,right in ((1,1,0),(-1,-1,0),(-2,-1,-2),(-3,-3,-2),(-4,-3,-4)):
        u,v,target = columns[left],columns[right],columns[index].copy()
        determinant = det(u[:,0],v[:,0])
        dd = [det(u[:,j],v[:,0])+det(u[:,0],v[:,j]) for j in (1,2)]
        columns[index][:,0] = target[:,0]/determinant
        for j in (1,2):
            columns[index][:,j] = target[:,j]/determinant-target[:,0]*dd[j-1]/determinant**2
    frames = []
    for a,b in ((1,0),(-1,0),(-1,-2),(-3,-2),(-3,-4)):
        frames.append([mp.matrix([[columns[a][0,j],columns[b][0,j]],
                                  [columns[a][1,j],columns[b][1,j]]]) for j in range(3)])
    ss, ds = [], []
    for k in range(4):
        left,right = frames[k],frames[k+1]
        inv = left[0]**-1
        matrix = inv*right[0]
        row,col = (1,0) if k%2 == 0 else (0,1)
        ss.append(matrix[row,col])
        ds.append([(inv*(right[j]-left[j]*matrix))[row,col] for j in (1,2)])
    products = mp.matrix([ss[a]*ss[b] for a,b in c.PAIRS])
    jac = mp.matrix([[ss[a]*ds[b][j]+ss[b]*ds[a][j] for j in range(2)] for a,b in c.PAIRS])
    return ss, products, jac


def contour_basis(x,state,p,radius=16,formal_order=48,tol='1e-30',coefficients=None):
    q,h,_,logq,logd = state[:5]
    root = mp.exp(logq/2)
    answers, saved = [], {}
    for name,spec in c.old.CYCLES.items():
        cols,pairs = [], []
        vertex_angle = mp.pi if name == 'B' else mp.mpf(0)
        for j in spec['indices']:
            values,pair = canonical_column(x,q,h,p,j,mp.mpf(radius),formal_order,mp.mpf(tol),root=root,vertex_angle=vertex_angle)
            gauge = mp.exp((1 if j%2 else -1)*logd)
            cols.append([v*gauge for v in values])
            pairs.append([v*gauge*gauge for v in pair])
        if coefficients is None:
            square = mp.matrix([[u[0]**2 for u in cols],
                                [u[0]*u[1] for u in cols],[u[1]**2 for u in cols]])
            # Cofactors give the null vector without a double-precision SVD.
            coef = [(-1)**j*mp.det(mp.matrix([[square[r,k] for k in range(4) if k != j] for r in range(3)])) for j in range(4)]
            scale = max(abs(v) for v in coef)
            coef = [v/scale for v in coef]
        else:
            coef = coefficients[name]
        saved[name] = coef
        answers.append([sum(coef[k]*pairs[k][r] for k in range(4)) for r in range(2)])
    return mp.matrix([[answers[0][0],answers[1][0]],[answers[0][1],answers[1][1]]]), saved


def tangent_conversion(x,state):
    q,h = state[:2]
    root = mp.exp(state[3]/2)
    qp = q*(2*h+q+2*x)
    return mp.matrix([[root,0],[-qp/(4*q*root)-root/2,1/(2*root)]])
