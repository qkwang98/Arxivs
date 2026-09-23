import Bridge.CertificateChecks
import Bridge.CertificateEnumeration
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace LiebBridge.Certificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def rationalWitnessForm (w : Witness) (d : Shape → ℚ) : ℚ :=
  (w.coefficients.map fun p => p.2 * d p.1).sum

def realWitnessForm (w : Witness) (d : Shape → ℝ) : ℝ :=
  (w.coefficients.map fun p => (p.2 : ℝ) * d p.1).sum

theorem rationalWeightedIdentity (d : Shape → ℚ) :
    (rows.map fun w => w.weight * rationalWitnessForm w d).sum =
      4035 * d [6, 5, 3] + 6725 * d [6, 4, 4] +
      39759 * d [5, 5, 4] + 23636 * d [5, 3, 3, 3] -
      59512 * d [4, 4, 3, 3] := by
  norm_num [rationalWitnessForm, rows, witness01, witness02, witness03, witness04, witness05, witness06, witness07, witness08, witness09, witness10, witness11, witness12, witness13, witness14, witness15, witness16, witness17, witness18, witness19, witness20]
  ring

theorem aggregateStoredIdentity (nu : Shape) :
    weightedStoredCoeff nu = identityCoeff nu := by
  have h := rationalWeightedIdentity (fun p => if nu = p then 1 else 0)
  by_cases ht : nu = [4, 4, 3, 3]
  all_goals
    simpa [rationalWitnessForm, weightedStoredCoeff, storedCoeff, sparseCoeff,
      identityCoeff, identityEntries, List.map_map, mul_ite,
      sub_eq_add_neg, add_assoc, ht] using h

theorem realWeightedIdentity (d : Shape → ℝ) :
    (rows.map fun w => (w.weight : ℝ) * realWitnessForm w d).sum =
      4035 * d [6, 5, 3] + 6725 * d [6, 4, 4] +
      39759 * d [5, 5, 4] + 23636 * d [5, 3, 3, 3] -
      59512 * d [4, 4, 3, 3] := by
  norm_num [realWitnessForm, rows, witness01, witness02, witness03, witness04, witness05, witness06, witness07, witness08, witness09, witness10, witness11, witness12, witness13, witness14, witness15, witness16, witness17, witness18, witness19, witness20]
  ring

/-- Pure arithmetic consequence. The twenty witness inequalities are explicit hypotheses;
this theorem makes no claim that they hold for actual matrix immanants. -/
theorem bridge_of_witness_nonnegative (d : Shape → ℝ)
    (hwitness : ∀ w ∈ rows, 0 ≤ realWitnessForm w d) :
    59512 * d [4, 4, 3, 3] ≤
      4035 * d [6, 5, 3] + 6725 * d [6, 4, 4] +
      39759 * d [5, 5, 4] + 23636 * d [5, 3, 3, 3] := by
  have hnonneg : 0 ≤ (rows.map fun w => (w.weight : ℝ) * realWitnessForm w d).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    apply mul_nonneg
    · exact_mod_cast (le_of_lt (weightsPositive w hw))
    · exact hwitness w hw
  rw [realWeightedIdentity] at hnonneg
  exact sub_nonneg.mp hnonneg

theorem computedCoeff_eq_storedCoeff_of_partition (w : Witness) (hw : w ∈ rows)
    (nu : Shape) (hnu : IsPartition14 nu) : computedCoeff w nu = storedCoeff w nu :=
  computedCoeff_eq_storedCoeff w hw nu (partitions14_complete nu hnu)

/-- Boolean guards for input shapes, distinct basis tableaux, and nonzero axial gaps. -/
def isPartitionOfCheck (n : Nat) (p : Shape) : Bool :=
  decide (p.sum = n) && decide (p.Pairwise (fun a b => b ≤ a)) &&
    p.all (fun a => decide (0 < a))

def witnessMetadataValid (w : Witness) : Bool :=
  decide (w.k = 1 ∨ w.k = 2) &&
    isPartitionOfCheck (14 - 2 * w.k) w.eta &&
    isPartitionOfCheck (14 - w.k) w.mu && contains w.mu w.eta &&
    decide (w.sign = 1 ∨ w.sign = -1)

def tableauDenominatorsValid (t : Tableau) : Bool :=
  (List.range (t.length - 1)).all fun i =>
    decide (content (t.getD (i + 1) (0, 0)) - content (t.getD i (0, 0)) ≠ 0)

def tableauBasisValid (w : Witness) (nu : Shape) : Bool :=
  let tabs := tableaux w.eta nu
  decide tabs.Nodup && tabs.all (fun t =>
    decide (t.length = 2 * w.k) && tableauDenominatorsValid t)

theorem witnessMetadataCheck : (rows.all witnessMetadataValid) = true := by
  decide +kernel

theorem tableauSafetyCheck :
    (rows.all fun w => partitions14.all (tableauBasisValid w)) = true := by
  decide +kernel

theorem rowEntriesPartitionCheck :
    (rows.all fun w => w.coefficients.all fun p => isPartition14Check p.1) = true := by
  decide +kernel

theorem rowEntriesDistinctCheck :
    (rows.all fun w => decide (w.coefficients.map Prod.fst).Nodup) = true := by
  decide +kernel

theorem rowEntriesNonzeroCheck :
    (rows.all fun w => w.coefficients.all fun p => decide (p.2 ≠ 0)) = true := by
  decide +kernel

theorem rowEntries_partition (w : Witness) (hw : w ∈ rows)
    (entry : Shape × ℚ) (he : entry ∈ w.coefficients) : IsPartition14 entry.1 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp rowEntriesPartitionCheck w hw) entry he
  simpa [IsPartition14, isPartition14Check, List.all_eq_true, and_assoc] using h

theorem storedCoeff_eq_zero_of_not_partition (w : Witness) (hw : w ∈ rows)
    (nu : Shape) (hnu : ¬ IsPartition14 nu) : storedCoeff w nu = 0 := by
  unfold storedCoeff sparseCoeff
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hx
  have hn : nu ≠ entry.1 := by
    intro hn
    apply hnu
    rw [hn]
    exact rowEntries_partition w hw entry he
  simp [hn]

theorem aggregateComputedIdentity (nu : Shape) (hnu : IsPartition14 nu) :
    weightedComputedCoeff nu = identityCoeff nu := by
  rw [← aggregateStoredIdentity]
  unfold weightedComputedCoeff weightedStoredCoeff
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  rw [computedCoeff_eq_storedCoeff_of_partition w hw nu hnu]

/-- A hook-formula arithmetic check only; identifying this function with irreducible
representation dimensions requires the separate hook-length theorem. -/
theorem hookDegree_square_sum :
    (partitions14.map fun p => (hookDegree p)^2).sum = Nat.factorial 14 := by
  decide +kernel

theorem rowHookDegreeCancellationCheck :
    (rows.all fun w =>
      ((w.coefficients.map fun p => p.2 * (hookDegree p.1 : ℚ)).sum == 0)) = true := by
  decide +kernel

end LiebBridge.Certificate
