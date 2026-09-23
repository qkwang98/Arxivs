import Bridge.Young.WitnessCoefficients
import Bridge.Young.WitnessTrace
import Bridge.Young.OrdinaryImmanants

/-! Assembly of the finite certificate row with the actual character expansion.
The remaining hypotheses are the concrete witness trace formula and positivity
of this same coefficient function against conjugated matrix coefficients. -/

noncomputable section
namespace LiebBridge.Young.WitnessCoefficientPositivity
open scoped BigOperators Classical
open Certificate WitnessShapes WitnessOperators WitnessCoefficients
open ConjugacyBound (Shape14)
open YoungCharacterCompleteness Bridge.CentralAveraging

theorem rowEntries_valid (w : Witness) (hw : w ∈ rows)
    (e : Shape × ℚ) (he : e ∈ w.coefficients) : IsPartition14 e.1 := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp rowEntriesPartitionCheck w hw) e he
  simpa [isPartition14Check, IsPartition14, List.all_eq_true, and_assoc] using h

theorem sum_sparseCoeff (entries : List (Shape × ℚ))
    (hvalid : ∀ e ∈ entries, IsPartition14 e.1) (d : Shape → ℝ) :
    (∑ p : Shape14, (sparseCoeff entries p.val : ℝ) * d p.val) =
      (entries.map fun e => (e.2 : ℝ) * d e.1).sum := by
  induction entries with
  | nil => simp [sparseCoeff]
  | cons e es ih =>
    have he := hvalid e (by simp)
    have hes : ∀ a ∈ es, IsPartition14 a.1 := fun a ha => hvalid a (by simp [ha])
    have htail := ih hes
    have hsingle : (∑ p : Shape14, ((if p.val = e.1 then e.2 else 0 : ℚ) : ℝ) *
        d p.val) = (e.2 : ℝ) * d e.1 := by
      let p0 : Shape14 := ⟨e.1, he⟩
      have heq (p : Shape14) : p.val = e.1 ↔ p = p0 :=
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simp_rw [heq]
      simp only [apply_ite, Rat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rfl
    simp only [sparseCoeff, List.map_cons, List.sum_cons, Rat.cast_add, add_mul,
      Finset.sum_add_distrib] at htail ⊢
    rw [hsingle, htail]

theorem sum_storedCoeff (w : Witness) (hw : w ∈ rows) (d : Shape → ℝ) :
    (∑ p : Shape14, (storedCoeff w p.val : ℝ) * d p.val) = realWitnessForm w d :=
  sum_sparseCoeff w.coefficients (rowEntries_valid w hw) d

def classPairing (m : S14 → ℝ) (p : Shape) : ℝ :=
  if hp : IsPartition14 p then pairing (character14 ⟨p,hp⟩) m else 0

@[simp]
theorem classPairing_valid (m : S14 → ℝ) (p : Shape14) :
    classPairing m p.val = pairing (character14 p) m := by
  simp only [classPairing, dif_pos p.property]

theorem coefficient_pairing_of_trace (w : Witness) (hw : w ∈ rows) (p : Shape14)
    (htrace : LinearMap.trace ℂ (Space p.val p.property) (witness w hw p.val p.property) =
      (YoungProjectors.degree (etaDiagram w hw) : ℂ) * (computedCoeff w p.val : ℂ)) :
    pairing (witnessCoeff w hw) (character14 p) =
      (YoungProjectors.degree (etaDiagram w hw) : ℝ) * (storedCoeff w p.val : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ratCast,
    ← computedCoeff_eq_storedCoeff_of_partition w hw p.val p.property,
    ← htrace, trace_witness_eq_pairing]

theorem coefficient_pairing (w : Witness) (hw : w ∈ rows) (p : Shape14) :
    pairing (witnessCoeff w hw) (character14 p) =
      (YoungProjectors.degree (etaDiagram w hw) : ℝ) * (storedCoeff w p.val : ℝ) :=
  coefficient_pairing_of_trace w hw p
    (WitnessTrace.trace_witness_eq_computedCoeff w hw p.val p.property)

/-- The arithmetic witness form is nonnegative once the same concrete
witness has the proved trace and a nonnegative conjugate pairing. -/
theorem realWitnessForm_nonneg_of_trace (w : Witness) (hw : w ∈ rows) (m : S14 → ℝ)
    (htrace : ∀ p : Shape14,
      LinearMap.trace ℂ (Space p.val p.property) (witness w hw p.val p.property) =
        (YoungProjectors.degree (etaDiagram w hw) : ℂ) * (computedCoeff w p.val : ℂ))
    (hpositive : ∀ a : S14,
      0 ≤ pairing (witnessCoeff w hw) (fun g => m (a*g*a⁻¹))) :
    0 ≤ realWitnessForm w (classPairing m) := by
  have h := character14_weighted_pairings_nonneg (witnessCoeff w hw) m hpositive
  simp_rw [coefficient_pairing_of_trace w hw _ (htrace _), mul_assoc] at h
  rw [← Finset.mul_sum] at h
  have he : (∑ p : Shape14, (storedCoeff w p.val : ℝ) * pairing (character14 p) m) =
      realWitnessForm w (classPairing m) := by
    simpa only [classPairing_valid] using sum_storedCoeff w hw (classPairing m)
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h (by
    exact_mod_cast Nat.pos_of_ne_zero (YoungProjectors.degree_ne_zero (etaDiagram w hw)))

theorem realWitnessForm_nonneg (w : Witness) (hw : w ∈ rows) (m : S14 → ℝ)
    (hpositive : ∀ a : S14,
      0 ≤ pairing (witnessCoeff w hw) (fun g => m (a*g*a⁻¹))) :
    0 ≤ realWitnessForm w (classPairing m) :=
  realWitnessForm_nonneg_of_trace w hw m
    (fun p => WitnessTrace.trace_witness_eq_computedCoeff w hw p.val p.property) hpositive

def realMonomial (A : Matrix14) (g : S14) : ℝ := (∏ i : Fin 14, A i (g i)).re

theorem immanant_eq_classPairing (A : Matrix14) :
    (fun p => OrdinaryImmanants.immanant p A) = classPairing (realMonomial A) := by
  funext p
  by_cases hp : IsPartition14 p
  · rw [OrdinaryImmanants.immanant_eq p hp]
    simp only [classPairing, dif_pos hp, realImmanant, complexImmanant,
      pairing, realMonomial, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  · simp [OrdinaryImmanants.immanant, OrdinaryImmanants.character, hp,
      realImmanant, complexImmanant, classPairing]

theorem ordinaryWitnessForm_nonneg (w : Witness) (hw : w ∈ rows) (A : Matrix14)
    (hpositive : ∀ a : S14,
      0 ≤ pairing (witnessCoeff w hw) (fun g => realMonomial A (a*g*a⁻¹))) :
    0 ≤ realWitnessForm w (fun p => OrdinaryImmanants.immanant p A) := by
  rw [immanant_eq_classPairing]
  exact realWitnessForm_nonneg w hw (realMonomial A) hpositive

end LiebBridge.Young.WitnessCoefficientPositivity
