"""PII (alpha=0): Taylor background, canonical columns, and squared cycles.

The author's source article is read-only. Contours here are finite sums of
subdominant rays with cancelling symmetric-square boundaries at lambda=0.
"""
from bisect import bisect_right

from mpmath import mp

from high_precision import conv, horner, step_radius


def reference_coefficients(x, state, order):
    series = [[v] for v in state]
    u, w, integral_u, y1, v1, y2, v2 = series
    square, potential = [], []
    for n in range(order):
        square.append(conv(u, u, n))
        potential.append(6*square[n]+(x if n == 0 else 1 if n == 1 else 0))
        rhs = [w[n], 2*conv(square, u, n)+x*u[n]+(u[n-1] if n else 0),
               u[n], v1[n], conv(potential, y1, n), v2[n], conv(potential, y2, n)]
        for seq, value in zip(series, rhs):
            seq.append(value/(n+1))
    return series


class Reference:
    def __init__(self, span=12, digits=70, tolerance='1e-36', order=40,
                 x0='-1', u0='.2', w0='.1'):
        self.digits, self.span = digits, mp.mpf(span)
        self.segments = []
        with mp.workdps(digits):
            self.x0 = mp.mpf(x0)
            self.initial = list(map(mp.mpf, [u0, w0, '0', '1', '0', '0', '1']))
            t, state = mp.mpf(0), self.initial
            while -t < self.span:
                cf = reference_coefficients(self.x0+t, state, order)
                step = -min(step_radius(cf, mp.mpf(tolerance), '.25'), self.span+t)
                if abs(step) < mp.mpf('1e-14'):
                    raise RuntimeError('PII reference step below floor')
                self.segments.append((t, t+step, cf))
                state = [horner(seq, step) for seq in cf]
                t += step
        self.starts = [abs(a) for a, _, _ in self.segments]

    def at(self, t):
        with mp.workdps(self.digits):
            t = mp.mpf(t)
            if t > 0 or -t > self.span:
                raise ValueError('PII reference defined on [-span, 0]')
            index = max(0, bisect_right(self.starts, -t)-1)
            origin, _, cf = self.segments[index]
            return [horner(seq, t-origin) for seq in cf]

    def potential(self, t):
        # Evaluate only the background, never reference linearized solutions.
        index = max(0, bisect_right(self.starts, -t)-1)
        origin, _, cf = self.segments[index]
        u = horner(cf[0], t-origin)
        return self.x0+t+6*u*u

    def matrix(self, t):
        s = self.at(t)
        return mp.matrix([[s[3], s[5]], [s[4], s[6]]])

    def anchor(self, t):
        # At lambda=0, B=u*sigma_1; these matrices commute for different x.
        z = self.at(t)[2]
        return mp.matrix([[mp.cosh(z), mp.sinh(z)], [mp.sinh(z), mp.cosh(z)]])


def formal_column(x, u, w, sign, order):
    """Riccati ratio and its amplitude, with leading coefficient exactly one.

sign=+1 is column 1, exp(-i*Omega); sign=-1 is column 2.
Only algebraic recurrence is used; no coefficients are copied from print.
"""
    ii = mp.j*sign
    r = [mp.mpc(0), ii*u/2, w/4]
    for m in range(1, order+1):
        lhs = -(m-1)*r[m-1] if m >= 2 else 0
        square_next = sum(r[k]*r[m+1-k] for k in range(1, m+1))
        square = sum(r[k]*r[m-k] for k in range(1, m))
        r.append((lhs-ii*(2*x+4*u*u)*r[m]+4*u*square_next+2*ii*w*square)/(8*ii))
    log_amp = [mp.mpc(0)]
    for n in range(1, order+1):
        log_amp.append(-(4*u*r[n+2]+2*ii*w*r[n+1])/n)
    amp = [mp.mpc(1)]
    for n in range(1, order+1):
        amp.append(sum(k*log_amp[k]*amp[n-k] for k in range(1, n+1))/n)
    other = [conv(r, amp, n) for n in range(order+1)]
    return [amp, other] if sign == 1 else [other, amp]


def spectral_coefficients(z, state, x, u, w, order, sensitivity=False):
    cf = [[v] for v in state]
    groups = 3 if sensitivity else 1
    diagonal = -mp.j*(4*z*z+x+2*u*u)
    upper, lower = 4*u*z+2*mp.j*w, 4*u*z-2*mp.j*w
    for n in range(order):
        for g in range(groups):
            a, b = cf[2*g:2*g+2]
            ra, rb = diagonal*a[n]+upper*b[n], lower*a[n]-diagonal*b[n]
            if n:
                ra += -8*mp.j*z*a[n-1]+4*u*b[n-1]
                rb += 4*u*a[n-1]+8*mp.j*z*b[n-1]
            if n >= 2:
                ra -= 4*mp.j*a[n-2]
                rb += 4*mp.j*b[n-2]
            if g == 1:
                ra += -4*mp.j*u*cf[0][n]+4*z*cf[1][n]
                rb += 4*z*cf[0][n]+4*mp.j*u*cf[1][n]
                if n:
                    ra += 4*cf[1][n-1]
                    rb += 4*cf[0][n-1]
            elif g == 2:
                ra += 2*mp.j*cf[1][n]
                rb -= 2*mp.j*cf[0][n]
            a.append(ra/(n+1))
            b.append(rb/(n+1))
    return cf


def kernel_coefficients(z, cf, u):
    a, b = cf[:2]
    out, dx, minus = [], [], []
    for n in range(len(a)-1):
        aa, bb, ab = conv(a, a, n), conv(b, b, n), conv(a, b, n)
        out.append(aa+bb)
        minus.append(aa-bb)
        dx.append(-2*mp.j*(z*minus[n]+(minus[n-1] if n else 0))+4*u*ab)
    return out, dx


def canonical(x, u, w, index, radius=4, formal_order=40, tolerance='1e-26',
              sensitivity=False, quadrature=True, order=32):
    angle = -mp.pi/6+index*mp.pi/3
    sign = 1 if index % 2 == 0 else -1
    z = mp.mpf(radius)*mp.exp(mp.j*angle)
    initial_z = z
    def initial(uu, ww):
        return [horner(cf, 1/z) for cf in formal_column(x, uu, ww, sign, formal_order)]
    state = initial(u, w)
    boundary = -mp.j*(state[0]**2-state[1]**2)/2
    if sensitivity:
        eps = mp.power(10, -mp.dps//3)
        for du, dw in ((eps, 0), (0, eps)):
            plus, minus = initial(u+du, w+dw), initial(u-du, w-dw)
            state.extend((a-b)/(2*eps) for a, b in zip(plus, minus))
    integrals = [mp.mpc(0), mp.mpc(0)]
    steps = 0
    while abs(z) > mp.mpf('1e-60'):
        cf = spectral_coefficients(z, state, x, u, w, order, sensitivity)
        size = min(step_radius(cf, mp.mpf(tolerance), '.4'), abs(z))
        step = -z/abs(z)*size
        if quadrature:
            for k, seq in enumerate(kernel_coefficients(z, cf, u)):
                integrals[k] += step*horner([v/(n+1) for n, v in enumerate(seq)], step)
        state = [horner(seq, step) for seq in cf]
        z += step
        steps += 1
        if steps > 30000:
            raise RuntimeError('PII spectral step budget exceeded')
    exponent = mp.exp(-sign*mp.j*(4*initial_z**3/3+x*initial_z))
    return {'column': mp.matrix([v*exponent for v in state[:2]]),
            'sensitivities': [mp.matrix([v*exponent for v in state[k:k+2]]) for k in (2, 4)]
                            if sensitivity else [],
            'integral': mp.matrix([v*exponent**2 for v in integrals]),
            'boundary': boundary*exponent**2, 'steps': steps}


def wedge(a, b):
    return a[0]*b[1]-a[1]*b[0]


def squared(column):
    a, b = column
    return mp.matrix([a*a, a*b, b*b])


def cycle_coefficients(columns):
    rows = mp.matrix([[squared(v)[k] for v in columns] for k in range(3)])
    cofactors = []
    for j in range(4):
        minor = mp.matrix([[rows[k, l] for l in range(4) if l != j] for k in range(3)])
        cofactors.append((-1)**j*mp.det(minor))
    scale = max(map(abs, cofactors))
    if not scale:
        raise ValueError('Degenerate four-ray cycle')
    return [v/scale for v in cofactors]


class Contours:
    groups = [(0, 1, 2, 3), (2, 3, 4, 5)]

    def __init__(self, reference, **settings):
        self.reference, self.settings = reference, settings
        self.base = self.columns(0)
        self.weights = [cycle_coefficients([self.base[j]['column'] for j in group])
                        for group in self.groups]
        self.initial_matrix, _ = self.assemble(self.base)
        self.inverse = self.initial_matrix**-1

    def columns(self, t):
        u, w = self.reference.at(t)[:2]
        x = self.reference.x0+t
        return [canonical(x, u, w, j, **self.settings) for j in range(6)]

    def assemble(self, data):
        matrix = mp.matrix(2, 2)
        boundary = mp.matrix(1, 2)
        for k, (group, weights) in enumerate(zip(self.groups, self.weights)):
            for j, c in zip(group, weights):
                for row in range(2):
                    matrix[row, k] += c*data[j]['integral'][row]
                boundary[k] -= c*data[j]['boundary']
        return matrix, boundary

    def at(self, t):
        data = self.columns(t) if t else self.base
        anchor = self.reference.anchor(t)
        direction_defect = mp.mpf(0)
        corrections = []
        for j, local in enumerate(data):
            target = anchor*self.base[j]['column']
            pivot = max(range(2), key=lambda k: abs(local['column'][k]))
            gamma = target[pivot]/local['column'][pivot]
            direction_defect = max(direction_defect,
                                   max(map(abs, gamma*local['column']-target))/max(map(abs, target)))
            corrections.append(abs(gamma-1))
            data[j] = dict(local, column=gamma*local['column'],
                           integral=gamma**2*local['integral'], boundary=gamma**2*local['boundary'])
        raw, boundary = self.assemble(data)
        inner = mp.mpf(0)
        for group, weights in zip(self.groups, self.weights):
            residual = sum((c*squared(data[j]['column']) for j, c in zip(group, weights)), mp.zeros(3, 1))
            scale = sum(abs(c)*max(map(abs, squared(data[j]['column']))) for j, c in zip(group, weights))
            inner = max(inner, max(map(abs, residual))/scale)
        return raw*self.inverse, {'direction_defect': direction_defect,
                                  'amplitude_correction': max(corrections),
                                  'inner_boundary_defect': inner,
                                  'outer_boundary': max(map(abs, boundary*self.inverse))}


def monodromy(x, u, w, **settings):
    """Four connection coefficients and their fixed-x (u,w) derivatives.

v[j+2] = a[j]*v[j] + b[j]*v[j+1]; b are Stokes coefficients
in the explicitly specified subdominant-column convention. No determinant
or conservation projection is applied. The four entries are redundant.
"""
    data = [canonical(x, u, w, j, sensitivity=True, quadrature=False, **settings) for j in range(6)]
    values, jacobian = mp.matrix(4, 1), mp.matrix(4, 2)
    adjacent = []
    for j in range(4):
        a, b, c = [data[k]['column'] for k in (j, j+1, j+2)]
        numerator, denominator = wedge(a, c), wedge(a, b)
        values[j] = numerator/denominator
        adjacent.append(abs(denominator-(-1)**j))
        for k in range(2):
            da, db, dc = [data[l]['sensitivities'][k] for l in (j, j+1, j+2)]
            dn = wedge(da, c)+wedge(a, dc)
            dd = wedge(da, b)+wedge(a, db)
            jacobian[j, k] = (dn*denominator-numerator*dd)/denominator**2
    return values, jacobian, max(adjacent)
