"""Independent checks of the finite-lambda normalization transport."""
import unittest

import numpy as np
from mpmath import mp

import anchored_psi as a


class AnchorTransportTests(unittest.TestCase):
    def test_B_transport_against_scipy(self):
        with mp.workdps(55):
            ref = a.hp.TaylorReference(.1,50,'1e-26')
            bg = a.hp.c.background(.1)
            for lam in (mp.mpf('1.45'),mp.mpf('-1.45')):
                transport = a.AnchorTransport(ref,lam)
                for sign in (-1,1):
                    def rhs(t,u):
                        q,h = bg(t)[:2]
                        return (a.hp.c.core.B_matrix(float(lam),a.hp.c.core.X0+t,q,h) @ u.reshape(2,2)).ravel()
                    sol = a.hp.c.ivp(rhs,(0,sign*.1),np.eye(2).ravel(),3e-14,method='DOP853')
                    value = transport.at(sign*.1)
                    np.testing.assert_allclose(np.array(value.tolist(),complex),sol.y[:,-1].reshape(2,2),rtol=2e-12,atol=2e-12)
                    self.assertLess(abs(mp.det(value)-1),mp.mpf('1e-28'))


if __name__ == '__main__':
    unittest.main()
