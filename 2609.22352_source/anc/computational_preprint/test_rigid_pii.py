import unittest

import numpy as np

from rigid_pii_pilot import initial_state,run,symbolic_checks


class RigidPIITests(unittest.TestCase):
    def test_symbolic_scalings_modes_and_general_parameter_kernel(self):
        result = symbolic_checks()
        self.assertGreater(abs(result['printed_second_mode_residual_at_theta1']),.5)

    def test_initial_data_use_the_lower_branch(self):
        state = initial_state(.01)
        self.assertLess(state[0],-1)
        self.assertGreater(state[1],0)
        np.testing.assert_array_equal(state[2:],[1,0,0,1])

    def test_first_pulse_and_determinant(self):
        result = run(.02)
        self.assertGreater(result['max_gain_balanced_input'],190)
        self.assertLess(result['max_gain_balanced_input'],197)
        self.assertLess(result['max_determinant_error'],2e-9)
        self.assertGreater(result['inner_peak_tau'],2.8)
        self.assertLess(result['inner_peak_tau'],2.85)


if __name__ == '__main__':
    unittest.main()
