import unittest

from mpmath import mp

from compare_rigid_oscillatory import post_drift


class PostTransitionDriftTests(unittest.TestCase):
    def test_constant_bias_is_not_post_transition_drift(self):
        with mp.workdps(50):
            offsets = [0., 1., 2.]
            jac = {s: mp.eye(2) for s in offsets}
            values = {0.: mp.eye(2), 1.: mp.eye(2)*mp.mpf('1.001'),
                      2.: mp.eye(2)*mp.mpf('1.001')}
            self.assertEqual(post_drift(values, jac, offsets, 1.)['max_row_drift'], 0)

    def test_change_of_direction_at_constant_error_norm_is_detected(self):
        with mp.workdps(50):
            offsets = [0., 1., 2.]
            jac = {s: mp.diag([mp.mpf('1e-20'), 1]) for s in offsets}
            values = {0.: mp.eye(2), 1.: mp.eye(2)*mp.mpf('1.001'),
                      2.: mp.eye(2)*mp.mpf('.999')}
            result = post_drift(values, jac, offsets, 1.)
            self.assertAlmostEqual(result['max_row_drift'], .002, places=15)
            self.assertAlmostEqual(result['points'][-1]['rows'][0], .002, places=15)


if __name__ == '__main__':
    unittest.main()
