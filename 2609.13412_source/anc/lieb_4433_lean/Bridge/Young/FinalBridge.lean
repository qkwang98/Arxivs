import Bridge.Young.TensorWitnessPositivity
import Bridge.Young.TensorPairing
import Bridge.Young.WitnessCoefficientPositivity

/-! The ordinary order-fourteen bridge on the entire Hermitian PSD cone.
The characters are internally defined from the constructed Young modules.
Only the four named historical Pate statements remain assumptions in the
final permanental-dominance transfer theorem. -/

noncomputable section
namespace LiebBridge.Young.FinalBridge
open scoped BigOperators Matrix ComplexOrder Classical
open Certificate WitnessCoefficients WitnessCoefficientPositivity
open YoungCharacterCompleteness TensorPairing

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem classPairing_moment (v : Fin 14 → D → ℂ) :
    classPairing (moment v) = fun p => OrdinaryImmanants.immanant p (gramMatrix v) := by
  funext p
  by_cases hp : IsPartition14 p
  · rw [classPairing, dif_pos hp, OrdinaryImmanants.immanant_eq p hp]
    exact character_pairing (character14 ⟨p,hp⟩)
      (fun g => YoungCharacter.realCharacter_inverse (WitnessShapes.partitionDiagram_card p hp) g) v
  · simp [classPairing, hp, OrdinaryImmanants.immanant, OrdinaryImmanants.character,
      realImmanant, complexImmanant]

/-- Every one of the twenty actual certificate rows is nonnegative on every
Gram matrix, with arbitrary complex vectors and arbitrary finite dimension. -/
theorem gram_witness_nonnegative (w : Witness) (hw : w ∈ rows)
    (v : Fin 14 → D → ℂ) :
    0 ≤ realWitnessForm w (fun p => OrdinaryImmanants.immanant p (gramMatrix v)) := by
  have hpositive := conjugated_pairing_nonneg (witnessCoeff w hw)
    (fun u => TensorWitnessPositivity.concrete_witness_nonneg w hw u) v
  have h := realWitnessForm_nonneg w hw (moment v) hpositive
  simpa only [classPairing_moment] using h

/-- Gram factorization covers the entire Hermitian PSD cone, including
singular matrices; no rank or genericity reduction is used. -/
theorem psd_witness_nonnegative (w : Witness) (hw : w ∈ rows)
    (A : Matrix14) (hA : A.PosSemidef) :
    0 ≤ realWitnessForm w (fun p => OrdinaryImmanants.immanant p A) := by
  obtain ⟨v, rfl⟩ := exists_gram_of_posSemidef A hA
  exact gram_witness_nonnegative w hw v

/-- The user's all-partition witness form, stated directly with the unchanged
computed tableau coefficients, is nonnegative on the entire PSD cone. -/
theorem computed_witness_nonnegative (w : Witness) (hw : w ∈ rows)
    (A : Matrix14) (hA : A.PosSemidef) :
    0 ≤ ∑ p : ConjugacyBound.Shape14,
      (computedCoeff w p.val : ℝ) * OrdinaryImmanants.immanant p.val A := by
  simp_rw [computedCoeff_eq_storedCoeff_of_partition w hw _ (Subtype.property _)]
  rw [sum_storedCoeff w hw (fun p => OrdinaryImmanants.immanant p A)]
  exact psd_witness_nonnegative w hw A hA

/-- The matrix bridge is proved for the internally constructed ordinary
character family; it is no longer an external hypothesis. -/
theorem matrix_bridge : Bridge4433 OrdinaryImmanants.character := by
  intro A hA
  exact bridge_of_witness_nonnegative (fun p => OrdinaryImmanants.immanant p A)
    (fun w hw => psd_witness_nonnegative w hw A hA)

theorem bridge_inequality (A : Matrix14) (hA : A.PosSemidef) :
    59512 * OrdinaryImmanants.immanant [4,4,3,3] A ≤
      4035 * OrdinaryImmanants.immanant [6,5,3] A +
      6725 * OrdinaryImmanants.immanant [6,4,4] A +
      39759 * OrdinaryImmanants.immanant [5,5,4] A +
      23636 * OrdinaryImmanants.immanant [5,3,3,3] A :=
  matrix_bridge A hA

theorem normalized_bridge (A : Matrix14) (hA : A.PosSemidef) :
    OrdinaryImmanants.immanant [4,4,3,3] A / 12012 ≤
      (20175 / 238048 : ℝ) * (OrdinaryImmanants.immanant [6,5,3] A / 15015) +
      (20175 / 238048 : ℝ) * (OrdinaryImmanants.immanant [6,4,4] A / 9009) +
      (79518 / 238048 : ℝ) * (OrdinaryImmanants.immanant [5,5,4] A / 6006) +
      (118180 / 238048 : ℝ) * (OrdinaryImmanants.immanant [5,3,3,3] A / 15015) :=
  normalizedBridge_of_matrixBridge OrdinaryImmanants.character matrix_bridge A hA

/-- Permanental dominance for `(4,4,3,3)`, conditional only on the four named
historical Pate statements for the same internally constructed characters.
There is no supplied character family, bridge, trace, or positivity hypothesis. -/
theorem pdc4433_of_four_pate
    (pate653 : Pate653 OrdinaryImmanants.character)
    (pate644 : Pate644 OrdinaryImmanants.character)
    (pate554 : Pate554 OrdinaryImmanants.character)
    (pate5333 : Pate5333 OrdinaryImmanants.character)
    (A : Matrix14) (hA : A.PosSemidef) :
    OrdinaryImmanants.immanant [4,4,3,3] A / 12012 ≤ permanent A :=
  pdc4433_of_bridge_and_four_pate OrdinaryImmanants.character matrix_bridge
    pate653 pate644 pate554 pate5333 A hA

end LiebBridge.Young.FinalBridge
