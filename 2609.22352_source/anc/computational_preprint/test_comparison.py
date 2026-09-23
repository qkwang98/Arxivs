"""Local consistency and independent finite-difference checks for the pilot."""
import unittest

import numpy as np

import compare_monodromy as c


class ComparisonTests(unittest.TestCase):
    def test_formal_and_spectral_derivatives(self):
        x, q, h, lam = c.core.X0, c.core.Q0, c.core.H0, 2.1+.6j
        eps = 1e-5
        args = (lam, x, q, h, c.core.THETA0, c.core.THETAINF)
        for function, start in ((c.core.Fhat, 0), (c.core.A_matrix, 2)):
            for axis in range(2):
                shift = np.eye(2)[axis]*eps
                plus = function(lam, x, *(np.array([q, h])+shift))
                minus = function(lam, x, *(np.array([q, h])-shift))
                np.testing.assert_allclose((plus-minus)/(2*eps),
                    c.DERIVATIVES[start+axis](*args), rtol=2e-8, atol=2e-9)

    def test_tangent_coordinate_change(self):
        bg = c.background(.02)
        eps = 1e-5
        def transform(t):
            q, h = bg(t)[:2]
            return c.tangent_conversion(c.core.X0+t, q, h)
        q, h = bg(0)[:2]
        x = c.core.X0
        a = np.array([[2*h+2*q+2*x, 2*q],
                      [-2*h+8*c.core.THETA0**2/q**3, -2*h-2*q-2*x]])
        b = np.array([[0, 1], [c.core.U_value(x, q), 0]])
        derivative = (transform(eps)-transform(-eps))/(2*eps)
        np.testing.assert_allclose(derivative+transform(0) @ b,
                                   a @ transform(0), rtol=2e-8, atol=2e-9)

    def test_spectral_sensitivity_against_finite_difference(self):
        q, h = c.core.Q0, c.core.H0
        direction = np.array([.19-.14j, -.16+.09j])
        _, m, jac = c.spectral_data(c.core.X0, q, h, 4.8, 2e-12)
        eps = 1e-4
        plus = c.spectral_data(c.core.X0, *(np.array([q, h])+eps*direction), 4.8, 2e-12)[1]
        minus = c.spectral_data(c.core.X0, *(np.array([q, h])-eps*direction), 4.8, 2e-12)[1]
        self.assertLess(c.scaled_max((plus-minus)/(2*eps)-jac @ direction, jac @ direction), 2e-7)
        # A product constraint and its differential; neither is an independent invariant.
        self.assertLess(abs(m[0]*m[2]-m[1]*m[3]), 1e-10)
        np.testing.assert_allclose(jac[0]*m[2]+m[0]*jac[2]-jac[1]*m[3]-m[1]*jac[3], 0, atol=1e-9)

    def test_monitor_detects_wrong_variation(self):
        grid = np.linspace(-.04, .04, 5)
        bg = c.background(.04)
        reference, _ = c.rk_matrix(grid, bg, 3e-14, "DOP853")
        _, _, jac, _ = c.spectral_profile(grid, bg, 4.8, 2e-12)
        good = c.summarize(reference, reference, jac)["monodromy_variation_drift"]
        bad = c.summarize(np.tile(np.eye(2), (5, 1, 1)), reference, jac)["monodromy_variation_drift"]
        self.assertLess(good, 1e-8)
        self.assertGreater(bad, 1e-3)

    def test_duhamel_quadrature_against_variational_equation(self):
        args = (c.core.X0, c.core.Q0, c.core.H0, 7.2, 2e-13)
        s, m, jac = c.spectral_data(*args)
        sq, mq, jq = c.spectral_data(*args, sensitivity="quadrature")
        self.assertLess(c.scaled_max(s-sq, s), 1e-9)
        self.assertLess(c.scaled_max(jac-jq, jac), 1e-9)

    def test_runge_kutta_refinement(self):
        grid = np.linspace(-.24, .24, 9)
        bg = c.background(.24)
        reference, _ = c.rk_matrix(grid, bg, 3e-14, "DOP853")
        coarse, _ = c.rk_matrix(grid, bg, 1e-3, "RK45")
        fine, _ = c.rk_matrix(grid, bg, 1e-9, "RK45")
        self.assertLess(np.max(abs(fine-reference)), .01*np.max(abs(coarse-reference)))


if __name__ == "__main__":
    unittest.main()
