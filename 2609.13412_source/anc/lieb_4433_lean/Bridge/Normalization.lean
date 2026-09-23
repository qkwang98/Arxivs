import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Numerical normalization of the order-fourteen bridge

This module proves only arithmetic implications for an arbitrary real-valued
function on lists of natural numbers. In an application, `d` is the
unnormalized ordinary immanant and `p` is the permanent. The definitions here
do not assert that any function is an immanant, that any matrix is positive
semidefinite, or that the bridge inequality has been proved.

The four previously established permanental-dominance results are explicit
hypotheses of the final theorem, separately named by their partitions.
-/

namespace Bridge.Normalization

def targetShape : List ℕ := [4, 4, 3, 3]
def shape653 : List ℕ := [6, 5, 3]
def shape644 : List ℕ := [6, 4, 4]
def shape554 : List ℕ := [5, 5, 4]
def shape5333 : List ℕ := [5, 3, 3, 3]

/-- The unnormalized bridge, with no division by a character degree or by `14!`. -/
def bridgeInequality (d : List ℕ → ℝ) : Prop :=
  59512 * d targetShape ≤
    4035 * d shape653 + 6725 * d shape644 +
      39759 * d shape554 + 23636 * d shape5333

/-- The same bridge expressed using normalized immanants and convex weights. -/
def normalizedBridgeInequality (d : List ℕ → ℝ) : Prop :=
  d targetShape / 12012 ≤
    (20175 / 238048 : ℝ) * (d shape653 / 15015) +
    (20175 / 238048 : ℝ) * (d shape644 / 9009) +
    (79518 / 238048 : ℝ) * (d shape554 / 6006) +
    (118180 / 238048 : ℝ) * (d shape5333 / 15015)

def PDC653 (d : List ℕ → ℝ) (p : ℝ) : Prop := d shape653 / 15015 ≤ p
def PDC644 (d : List ℕ → ℝ) (p : ℝ) : Prop := d shape644 / 9009 ≤ p
def PDC554 (d : List ℕ → ℝ) (p : ℝ) : Prop := d shape554 / 6006 ≤ p
def PDC5333 (d : List ℕ → ℝ) (p : ℝ) : Prop := d shape5333 / 15015 ≤ p
def PDC4433 (d : List ℕ → ℝ) (p : ℝ) : Prop := d targetShape / 12012 ≤ p

/-- Exact degree balance; this is why the normalized coefficients sum to one. -/
theorem degree_balance :
    (59512 : ℕ) * 12012 =
      4035 * 15015 + 6725 * 9009 + 39759 * 6006 + 23636 * 15015 := by
  norm_num

theorem normalized_weights_positive :
    (0 : ℝ) < 20175 / 238048 ∧
    (0 : ℝ) < 20175 / 238048 ∧
    (0 : ℝ) < 79518 / 238048 ∧
    (0 : ℝ) < 118180 / 238048 := by
  norm_num

theorem normalized_weights_sum :
    (20175 / 238048 : ℝ) + (20175 / 238048 : ℝ) +
      (79518 / 238048 : ℝ) + (118180 / 238048 : ℝ) = 1 := by
  norm_num

/-- The unnormalized and normalized bridge propositions are exactly equivalent. -/
theorem bridge_iff_normalizedBridge (d : List ℕ → ℝ) :
    bridgeInequality d ↔ normalizedBridgeInequality d := by
  unfold bridgeInequality normalizedBridgeInequality
  constructor <;> intro h <;> linarith only [h]

theorem normalizedBridge_of_bridge {d : List ℕ → ℝ}
    (h : bridgeInequality d) : normalizedBridgeInequality d :=
  (bridge_iff_normalizedBridge d).mp h

theorem bridge_of_normalizedBridge {d : List ℕ → ℝ}
    (h : normalizedBridgeInequality d) : bridgeInequality d :=
  (bridge_iff_normalizedBridge d).mpr h

/-- A convex bridge transfers the four explicit PDC hypotheses to the target. -/
theorem pdc4433_of_normalizedBridge {d : List ℕ → ℝ} {p : ℝ}
    (hbridge : normalizedBridgeInequality d)
    (h653 : PDC653 d p) (h644 : PDC644 d p)
    (h554 : PDC554 d p) (h5333 : PDC5333 d p) : PDC4433 d p := by
  unfold normalizedBridgeInequality at hbridge
  unfold PDC653 at h653
  unfold PDC644 at h644
  unfold PDC554 at h554
  unfold PDC5333 at h5333
  unfold PDC4433
  linarith only [hbridge, h653, h644, h554, h5333]

/-- The application-facing arithmetic implication, conditional on the bridge
and precisely the four previously established PDC statements. -/
theorem pdc4433_of_bridge {d : List ℕ → ℝ} {p : ℝ}
    (hbridge : bridgeInequality d)
    (h653 : PDC653 d p) (h644 : PDC644 d p)
    (h554 : PDC554 d p) (h5333 : PDC5333 d p) : PDC4433 d p :=
  pdc4433_of_normalizedBridge (normalizedBridge_of_bridge hbridge)
    h653 h644 h554 h5333

end Bridge.Normalization
