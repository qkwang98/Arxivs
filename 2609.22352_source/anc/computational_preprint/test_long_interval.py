"""Checks for the lifted square-root chart used in long continuation."""
import unittest

import numpy as np

import compare_monodromy as c
from long_interval import LiftedBackground


class LiftedBackgroundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bg = LiftedBackground(3.)

    def root(self, t):
        return self.bg.sheet(t)*np.sqrt(self.bg(t)[0])

    def test_initial_sheet_and_pilot_chart(self):
        self.assertEqual(self.bg.sheet(0), 1.)
        for t in np.linspace(-.6, .6, 31):
            self.assertEqual(self.bg.sheet(t), 1.)

    def test_logarithm_and_square(self):
        for t in np.linspace(-3, 3, 121):
            state = self.bg.state(t)
            self.assertLess(abs(np.exp(state[3])/state[0]-1), 1e-9)
            self.assertLess(abs(self.root(t)**2/state[0]-1), 1e-14)

    def test_continuity_across_principal_cut(self):
        grid = np.linspace(-3, 3, 3001)
        q = np.array([self.bg(t)[0] for t in grid])
        crossings = np.flatnonzero(abs(np.diff(np.angle(q))) > np.pi)
        self.assertGreater(len(crossings), 0)
        for k in crossings:
            self.assertEqual(self.bg.sheet(grid[k]), -self.bg.sheet(grid[k+1]))
            self.assertLess(abs(self.root(grid[k+1])/self.root(grid[k])-1), .1)

    def test_lifted_tangent_coordinate_change(self):
        for t in (-2.5, -1., .8, 2., 2.8):
            eps = 1e-6
            def transform(v):
                q, h = self.bg(v)[:2]
                return self.bg.sheet(v)*c.tangent_conversion(c.core.X0+v, q, h)
            q, h = self.bg(t)[:2]
            x = c.core.X0+t
            tangent = np.array([[2*h+2*q+2*x, 2*q],
                                [-2*h+8*c.core.THETA0**2/q**3, -2*h-2*q-2*x]])
            normal = np.array([[0, 1], [c.core.U_value(x, q), 0]])
            derivative = (transform(t+eps)-transform(t-eps))/(2*eps)
            np.testing.assert_allclose(derivative+transform(t) @ normal,
                                       tangent @ transform(t), rtol=2e-7, atol=2e-7)


if __name__ == "__main__":
    unittest.main()
