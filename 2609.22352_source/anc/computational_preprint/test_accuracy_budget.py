import unittest

from mpmath import mp

from accuracy_budget import assess
import high_precision as hp
from parameter_study import norm, refinement_budget


class AccuracyBudgetTests(unittest.TestCase):
    def test_budget_acceptance_and_attribution(self):
        d = dict(contour_increment='1e-12', previous_contour_increment='1e-9',
                 reference_increment='1e-15', monitor_increment='1e-15',
                 reference_conservation_defect='1e-16')
        self.assertTrue(assess(d, '1e-10')['accepted'])
        d['monitor_increment'] = '1e-8'
        self.assertEqual(assess(d, '1e-10')['failed_checks'], ['monitor_increment'])

    def test_stagnation_and_invalid_values(self):
        d = dict(contour_increment='1e-12', previous_contour_increment='1e-12',
                 reference_increment=0, monitor_increment=0, reference_conservation_defect=0)
        self.assertIn('contraction', assess(d, '1e-10')['failed_checks'])
        d['previous_contour_increment'] = 0
        self.assertFalse(assess(d, '1e-10')['accepted'])
        for v in ('nan', '-1', 'inf'):
            with self.assertRaises(ValueError):
                assess(dict(d, monitor_increment=v), '1e-10')
        with self.assertRaises(ValueError):
            assess(d, 0)

    def test_exact_initial_normalization_identity(self):
        with mp.workdps(50):
            phi = mp.matrix([[2,1],[1,3]])
            base = mp.matrix([[1,2],[0,1]])
            dphi = mp.matrix([[mp.mpf('1e-5'),0],[0,0]])
            dbase = mp.matrix([[0,0],[mp.mpf('1e-6'),0]])
            f = phi*base**-1
            actual = (phi+dphi)*(base+dbase)**-1-f
            identity = (dphi-f*dbase)*(base+dbase)**-1
            self.assertLess(norm(actual-identity), mp.mpf('1e-45'))

    def test_budget_uses_actual_matrix_products(self):
        j = {0:mp.eye(2), 1:mp.matrix([[100,0],[0,1]])}
        f = {0:mp.eye(2), 1:mp.matrix([[mp.mpf('.01'),0],[0,1]])}
        coarse = {k:v.copy() for k,v in f.items()}
        coarse[1][0,0] += mp.mpf('.001')
        budget = refinement_budget(coarse, f, f, j, j, f)
        self.assertAlmostEqual(float(budget['contour_increment']), .1)
        self.assertEqual(budget['reference_conservation_defect'], 0)

    def test_custom_piv_parameters_are_used(self):
        with mp.workdps(50):
            p = hp.Parameters()
            original = p.a
            p.a += mp.mpf('.02')
            ref = hp.TaylorReference(.01, 50, '1e-28', 32, parameters=p)
            self.assertEqual(ref.p.a, original+mp.mpf('.02'))
            self.assertEqual(hp.Parameters().a, original)
            cf = hp.reference_coefficients(p.x0, ref.initial, p, 2)
            expected = -p.h0**2-2*p.h0*(p.q0+p.x0)-2*p.b-4*p.a**2/p.q0**2
            self.assertLess(abs(cf[1][1]-expected), mp.mpf('1e-45'))


if __name__ == '__main__':
    unittest.main()
