import unittest

from mpmath import mp
import numpy as np
from scipy.integrate import solve_ivp

import pii_core as pii
import rigid_monodromy as r


class GeneralPIIMonodromyTests(unittest.TestCase):
    def test_zero_parameter_formal_coefficients(self):
        with mp.workdps(60):
            x,q,w = map(mp.mpf,['-.7','.2','.1'])
            for sign in (1,-1):
                old = pii.formal_column(x,q,w,sign,24)
                new = r.formal_column(x,q,w,mp.mpf(0),sign,24)
                self.assertLess(max(abs(a-b) for aa,bb in zip(old,new) for a,b in zip(aa,bb)),mp.mpf('1e-50'))

    def test_general_parameter_formal_recurrence(self):
        with mp.workdps(70):
            x,q,w,alpha = mp.mpf('.7'),mp.mpc('.2','.1'),mp.mpc('.1','-.2'),mp.mpc('.3','.4')
            columns = [r.formal_column(x,q,w,alpha,sign,18) for sign in (1,-1)]
            matrices = [mp.matrix([[columns[j][i][n] for j in range(2)] for i in range(2)]) for n in range(19)]
            s3,s1 = mp.diag([1,-1]),mp.matrix([[0,1],[1,0]])
            a0 = mp.matrix([[-mp.j*(x+2*q*q),2*mp.j*w],[-2*mp.j*w,mp.j*(x+2*q*q)]])
            for k in range(17):
                rhs = -4*mp.j*(s3*matrices[k+2]-matrices[k+2]*s3)+4*q*s1*matrices[k+1]+a0*matrices[k]+mp.j*x*matrices[k]*s3
                if k:
                    rhs -= alpha*s1*matrices[k-1]
                lhs = -(k-1)*matrices[k-1] if k else mp.zeros(2)
                self.assertLess(max(map(abs,lhs-rhs)),mp.mpf('1e-50'))
            H = x*q*q+q**4-w*w+2*alpha*q
            self.assertLess(abs(matrices[1][0,0]-mp.j*H/2),mp.mpf('1e-60'))

    def test_background_and_unitary_anchor(self):
        with mp.workdps(70):
            ref = r.Reference(end='-6.95',digits=70)
            eps = float(ref.epsilon)
            def rhs(t,y):
                u,p = y[:2]
                k = 6*u*u+t
                return np.array([p,1-2*u**3-t*u,y[3],-k*y[2],y[5],-k*y[4]])/eps
            sol = solve_ivp(rhs,(-7,-6.95),list(map(float,ref.initial)),method='DOP853',rtol=2e-13,atol=2e-14)
            self.assertTrue(sol.success)
            self.assertLess(max(abs(float(a)-b) for a,b in zip(ref.at(ref.end),sol.y[:,-1])),1e-12)
            anchor = r.Anchor(ref,'1.5').at(ref.end)
            self.assertLess(max(map(abs,anchor.H*anchor-mp.eye(2))),mp.mpf('1e-28'))

    def test_spectral_sensitivities_at_nonzero_vertex(self):
        with mp.workdps(70):
            x,q,w,alpha = mp.mpf('-.7'),mp.mpf('.2'),mp.mpf('.1'),mp.j*mp.mpf('.3')
            settings = dict(radius=3,formal_order=30,tolerance='1e-30',order=36)
            base = r.canonical(x,q,w,alpha,0,sensitivity=True,**settings)
            h = mp.mpf('1e-10')
            for k,(dq,dw) in enumerate(((h,0),(0,h))):
                plus = r.canonical(x,q+dq,w+dw,alpha,0,**settings)['column']
                minus = r.canonical(x,q-dq,w-dw,alpha,0,**settings)['column']
                self.assertLess(max(map(abs,(plus-minus)/(2*h)-base['sensitivities'][k])),mp.mpf('1e-16'))


if __name__ == '__main__':
    unittest.main()
