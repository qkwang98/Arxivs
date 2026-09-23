"""Validate the high-precision RK tableau and adaptive integration."""
import unittest

import numpy as np
from mpmath import mp
from scipy.integrate._ivp.rk import RK45,rk_step as scipy_step

import rk45_multiprecision as rk


class MultiprecisionRKTests(unittest.TestCase):
    def test_tableau_matches_scipy(self):
        with mp.workdps(60):
            aa,bb,cc,ee = rk.tableau()
            for row,expected in zip(aa,RK45.A):
                np.testing.assert_allclose([float(v) for v in row],expected[:len(row)],rtol=0,atol=0)
            for values,expected in ((bb,RK45.B),(cc,RK45.C),(ee,RK45.E)):
                np.testing.assert_allclose([float(v) for v in values],expected,rtol=0,atol=0)
            self.assertLess(abs(sum(bb)-1),mp.mpf('1e-55'))

    def test_one_step_matches_scipy(self):
        with mp.workdps(50):
            def fun(t,y):
                return [(t+mp.mpf('.3'))*y[0]+y[1],-y[0]+t*y[1]]
            t,step = mp.mpf('.2'),mp.mpf('.03')
            y = [mp.mpc('.8','.1'),mp.mpc('-.3','.2')]
            value,fn,error = rk.rk_step(fun,t,y,fun(t,y),step,rk.tableau())
            def double_fun(t,y):
                return np.array([(t+.3)*y[0]+y[1],-y[0]+t*y[1]])
            yd = np.array([complex(v) for v in y])
            stages = np.empty((7,2),complex)
            expected,_ = scipy_step(double_fun,float(t),yd,double_fun(float(t),yd),float(step),RK45.A,RK45.B,RK45.C,stages)
            np.testing.assert_allclose([complex(v) for v in value],expected,rtol=2e-15,atol=2e-15)
            np.testing.assert_allclose([complex(v) for v in error],float(step)*RK45.E @ stages,rtol=1e-6,atol=2e-17)

    def test_adaptive_order_and_backward_solution(self):
        with mp.workdps(60):
            errors = []
            for tol in ('1e-10','1e-15'):
                values,stats = rk.integrate(lambda t,y:[y[0]],[-1.,0.,1.],[mp.mpf(1)],tol)
                errors.append(max(abs(values[t][0]-mp.exp(t)) for t in (-1.,1.)))
                self.assertGreater(stats['accepted_steps'],0)
            self.assertLess(errors[1],errors[0]/1000)
            self.assertLess(errors[1],mp.mpf('1e-14'))

    def test_local_piv_reference(self):
        with mp.workdps(60):
            ref = rk.hp.TaylorReference(.1,60,'1e-30',32)
            values,_ = rk.fundamental(ref,[-.1,0.,.1],'1e-16')
            for t in (-.1,.1):
                self.assertLess(max(abs(v) for v in values[t]-ref.matrix(t)),mp.mpf('1e-15'))


if __name__ == '__main__':
    unittest.main()
