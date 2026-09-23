"""Checks of algebraic Taylor recurrences and local spectral quadrature."""
import unittest

import numpy as np
from mpmath import mp
from scipy.integrate import quad_vec

import high_precision as hp


class HighPrecisionTests(unittest.TestCase):
    def setUp(self):
        self.context = mp.workdps(55)
        self.context.__enter__()
        self.p = hp.Parameters()

    def tearDown(self):
        self.context.__exit__(None,None,None)

    def test_formal_coefficients_and_recurrence(self):
        p = self.p
        f = hp.formal_series(p.x0,p.q0,p.h0,p,12)
        old = hp.c.core.formal_coefficients(hp.c.core.X0,hp.c.core.Q0,hp.c.core.H0)
        for n in (1,2):
            np.testing.assert_allclose(np.array(f[n].tolist(),complex),old[n-1],atol=1e-15,rtol=1e-15)
        a0,d = hp.lax_parts(p.x0,p.q0,p.h0,p)
        z = mp.matrix([[1,0],[0,-1]])
        for n in range(1,12):
            residual = ((n-1)*f[n-1]+z*f[n+1]-f[n+1]*z
                        +a0*f[n]-p.x0*f[n]*z+d*f[n-1]+p.b*f[n-1]*z)
            self.assertLess(max(abs(v) for v in residual),mp.mpf('1e-40'))

    def test_reference_against_local_scipy_and_invariants(self):
        ref = hp.TaylorReference(.1,50,'1e-26')
        bg = hp.c.background(.1)
        grid = np.linspace(-.1,.1,5)
        ff,_ = hp.c.rk_matrix(grid,bg,3e-14,'DOP853')
        for i,t in enumerate(grid):
            state = ref.at(float(t))
            np.testing.assert_allclose(np.array([complex(v) for v in state[:2]]),bg(t)[:2],rtol=2e-12,atol=2e-12)
            np.testing.assert_allclose(np.array(ref.matrix(float(t)).tolist(),complex),ff[i],rtol=2e-12,atol=2e-12)
            self.assertLess(abs(state[0]*state[2]-1),mp.mpf('1e-28'))
            self.assertLess(abs(mp.exp(state[3])/state[0]-1),mp.mpf('1e-28'))
            self.assertLess(abs(mp.det(ref.matrix(float(t)))-1),mp.mpf('1e-28'))

    def test_spectral_taylor_and_kernel_quadrature(self):
        p = self.p
        start,end = mp.mpc('1.45','.1'),mp.mpc('1.62','.18')
        u0 = [mp.mpc('.8','.2'),mp.mpc('-.3','.1')]
        values,integrals = hp.spectral_path(u0,[start,end],p.x0,p.q0,p.h0,p,
                                           mp.mpf('1e-26'),root=mp.sqrt(p.q0))
        z0,dz = complex(start),complex(end-start)
        def rhs(t,u):
            return dz*(hp.c.core.A_matrix(z0+t*dz,hp.c.core.X0,hp.c.core.Q0,hp.c.core.H0) @ u)
        sol = hp.c.ivp(rhs,(0,1),[complex(v) for v in u0],3e-14,method='DOP853',dense_output=True)
        def kernel(t):
            lam,u = z0+t*dz,sol.sol(t)
            return dz*np.array([hp.c.core.Q_value(lam,hp.c.core.X0,hp.c.core.Q0,hp.c.core.H0,u),
                                hp.c.old.q_x_value(lam,hp.c.core.X0,hp.c.core.Q0,hp.c.core.H0,u)])
        pair,_ = quad_vec(kernel,0,1,epsabs=1e-13,epsrel=1e-13)
        np.testing.assert_allclose([complex(v) for v in values],sol.y[:,-1],atol=2e-12,rtol=2e-12)
        np.testing.assert_allclose([complex(v) for v in integrals],pair,atol=2e-12,rtol=2e-12)

    def test_spectral_sensitivities(self):
        p = self.p
        _,_,jac = hp.monodromy(p.x0,p.q0,p.h0,p,6,20,'1e-24')
        _,_,old = hp.c.spectral_data(hp.c.core.X0,hp.c.core.Q0,hp.c.core.H0,6,2e-13)
        np.testing.assert_allclose(np.array(jac.tolist(),complex),old,rtol=2e-10,atol=2e-10)


if __name__ == '__main__':
    unittest.main()
