import unittest

from mpmath import mp
import sympy as sp

import pii_core as p


class PIIIdentities(unittest.TestCase):
    def test_energy_derivative(self):
        t, u, w = sp.symbols('t u w', real=True)
        energy = w*w/2+t*u*u/2-u**4/2
        derivative = sp.diff(energy,t)+sp.diff(energy,u)*w+sp.diff(energy,w)*(2*u**3-t*u)
        self.assertEqual(sp.expand(derivative-u*u/2),0)

    def test_zero_curvature_and_squared_kernel(self):
        x, z, u, w, a, b, v, vp = sp.symbols('x z u w a b v vp')
        ii = sp.I
        A = sp.Matrix([[-ii*(4*z*z+x+2*u*u), 4*u*z+2*ii*w],
                       [4*u*z-2*ii*w, ii*(4*z*z+x+2*u*u)]])
        B = sp.Matrix([[-ii*z, u], [u, ii*z]])
        Ax = A.diff(x)+A.diff(u)*w+A.diff(w)*(2*u**3+x*u)
        self.assertEqual(sp.simplify(Ax-B.diff(z)+A*B-B*A), sp.zeros(2))
        az, bz = A*sp.Matrix([a, b])
        ax, bx = B*sp.Matrix([a, b])
        def dx(expr):
            return sp.diff(expr,x)+sp.diff(expr,u)*w+sp.diff(expr,w)*(2*u**3+x*u)+sp.diff(expr,a)*ax+sp.diff(expr,b)*bx+sp.diff(expr,v)*vp+sp.diff(expr,vp)*(6*u*u+x)*v
        def dz(expr):
            return sp.diff(expr,z)+sp.diff(expr,a)*az+sp.diff(expr,b)*bz
        K, R = a*a+b*b, -ii*(a*a-b*b)/2
        self.assertEqual(sp.expand(dx(dx(K))-(6*u*u+x)*K-dz(R)), 0)
        variation = 4*z*v*(a*a-b*b)-2*ii*vp*K+8*ii*u*v*a*b
        self.assertEqual(sp.expand(dx(variation)-v*dz(a*a-b*b)), 0)

    def test_formal_first_coefficient(self):
        with mp.workdps(60):
            x, u, w = map(mp.mpf, ['-.7', '.2', '.1'])
            H = x*u*u+u**4-w*w
            for sign in (1, -1):
                cf = p.formal_column(x, u, w, sign, 4)
                diagonal, other = cf if sign == 1 else cf[::-1]
                self.assertLess(abs(diagonal[1]-sign*mp.j*H/2), mp.mpf('1e-55'))
                self.assertLess(abs(other[1]-sign*mp.j*u/2), mp.mpf('1e-55'))

    def test_formal_matrix_recurrence(self):
        with mp.workdps(60):
            x, u, w = map(mp.mpf, ['-.7', '.2', '.1'])
            columns = [p.formal_column(x, u, w, sign, 16) for sign in (1, -1)]
            matrices = [mp.matrix([[columns[j][i][n] for j in range(2)] for i in range(2)])
                        for n in range(17)]
            s3, s1 = mp.matrix([[1,0],[0,-1]]), mp.matrix([[0,1],[1,0]])
            a0 = mp.matrix([[-mp.j*(x+2*u*u), 2*mp.j*w],[-2*mp.j*w, mp.j*(x+2*u*u)]])
            for k in range(15):
                rhs = -4*mp.j*(s3*matrices[k+2]-matrices[k+2]*s3)+4*u*s1*matrices[k+1]+a0*matrices[k]+mp.j*x*matrices[k]*s3
                lhs = -(k-1)*matrices[k-1] if k else mp.zeros(2)
                self.assertLess(max(map(abs, rhs-lhs)), mp.mpf('1e-50'))

    def test_airy_reference(self):
        with mp.workdps(60):
            ref = p.Reference(span=2, digits=60, tolerance='1e-32', u0='0', w0='0')
            def airy(x):
                return mp.matrix([[mp.airyai(x), mp.airybi(x)],
                                  [mp.airyai(x,1), mp.airybi(x,1)]])
            truth = airy(-3)*airy(-1)**-1
            self.assertLess(max(map(abs, ref.matrix(-2)-truth)), mp.mpf('1e-30'))
            self.assertEqual(ref.at(-2)[0], 0)

    def test_cycle_cancels_symmetric_boundary(self):
        with mp.workdps(50):
            columns = [mp.matrix(v) for v in ([1,0], [0,1], [1,1], [2,-1])]
            cc = p.cycle_coefficients(columns)
            residual = sum((c*p.squared(v) for c,v in zip(cc, columns)), mp.zeros(3,1))
            self.assertLess(max(map(abs, residual)), mp.mpf('1e-45'))

    def test_airy_contour_value_and_derivative(self):
        with mp.workdps(60):
            values = [p.canonical(mp.mpf('-1'), mp.mpf(0), mp.mpf(0), j,
                                  radius=3, formal_order=0, tolerance='1e-27')['integral']
                      for j in (4, 0)]
            integral = values[0]-values[1]
            truth = mp.pi*mp.matrix([mp.airyai(-1), mp.airyai(-1, 1)])
            self.assertLess(max(map(abs, integral-truth)), mp.mpf('1e-26'))

    def test_spectral_sensitivities(self):
        with mp.workdps(65):
            x, u, w = map(mp.mpf, ['-1', '.2', '.1'])
            settings = dict(radius=3, formal_order=30, tolerance='1e-30', quadrature=False)
            value = p.canonical(x, u, w, 0, sensitivity=True, **settings)
            eps = mp.mpf('1e-12')
            for k, (du, dw) in enumerate(((eps,0),(0,eps))):
                plus = p.canonical(x, u+du, w+dw, 0, **settings)['column']
                minus = p.canonical(x, u-du, w-dw, 0, **settings)['column']
                error = max(map(abs, (plus-minus)/(2*eps)-value['sensitivities'][k]))
                self.assertLess(error, mp.mpf('1e-20'))

    def test_long_contour_basis_with_quadrature_control(self):
        with mp.workdps(70):
            ref = p.Reference()
            contours = p.Contours(ref,radius=4,formal_order=48,tolerance='1e-6')
            result, diagnostics = contours.at(-12)
            error = max(map(abs,result-ref.matrix(-12)))/max(map(abs,ref.matrix(-12)))
            self.assertLess(error, mp.mpf('1e-8'))
            self.assertGreater(abs(mp.det(contours.initial_matrix)), 1)
            self.assertLess(diagnostics['inner_boundary_defect'],mp.mpf('1e-12'))


if __name__ == '__main__':
    unittest.main()
