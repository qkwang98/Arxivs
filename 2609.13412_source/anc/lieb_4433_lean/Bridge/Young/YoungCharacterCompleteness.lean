import Bridge.Young.ConjugacyBound
import Bridge.Young.ClassFunctionCompleteness
import Bridge.Young.YoungFDRep
import Bridge.Young.YoungCharacter

/-! Completeness of the actual rational Young characters for `S₁₄`.
The constructed, proved-simple representations have 135 orthogonal characters.
The conjugacy-class upper bound then proves spanning of all real class functions.
No hook formula, character table identification, or completeness premise is used. -/

noncomputable section
namespace LiebBridge.Young.YoungCharacterCompleteness
open scoped BigOperators
open ConjugacyBound WitnessShapes Bridge.CentralAveraging

local instance : DecidableEq Shape14 := Classical.decEq _
local instance : Fintype (ConjClasses S14) := by
  letI := Finite.of_injective conjugacyShape conjugacyShape_injective
  exact Fintype.ofFinite _

def character14 (p : Shape14) : S14 → ℝ :=
  YoungCharacter.realCharacter (n := 13) (partitionDiagram_card p.val p.property)

theorem partitionDiagram_eq_iff (p q : Shape14) :
    partitionDiagram p.val p.property = partitionDiagram q.val q.property ↔ p = q := by
  constructor
  · intro h
    apply Subtype.ext
    simpa only [partitionDiagram_rowLens] using congrArg YoungDiagram.rowLens h
  · rintro rfl
    rfl

theorem character14_isClassFunction (p : Shape14) : IsClassFunction (character14 p) := by
  intro a g
  unfold character14 YoungCharacter.realCharacter YoungCharacter.rationalCharacter
  congr 1
  simpa only [inv_inv] using
    FDRep.char_conj (FDRep.of (YoungRepresentation.representation
      (n := 13) (partitionDiagram_card p.val p.property))) g a⁻¹

theorem character14_orthogonal : CharacterOrthogonal character14 := by
  classical
  intro p q
  have hc := YoungFDRep.char_orthonormal ℂ
    (n := 13) (partitionDiagram_card p.val p.property)
    (partitionDiagram_card q.val q.property)
  simp_rw [YoungCharacter.complex_character_eq_real,
    YoungCharacter.realCharacter_inverse] at hc
  rw [partitionDiagram_eq_iff] at hc
  have hr : (Fintype.card S14 : ℝ)⁻¹ *
      ∑ g : S14, character14 p g * character14 q g = if p = q then 1 else 0 := by
    apply Complex.ofReal_injective
    push_cast
    split_ifs at hc ⊢ <;> simpa only [character14, Complex.ofReal_one,
      Complex.ofReal_zero] using hc
  have hcard : (Fintype.card S14 : ℝ) ≠ 0 := by positivity
  have hm := congrArg (fun x : ℝ => (Fintype.card S14 : ℝ) * x) hr
  simpa only [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_ite, mul_one, mul_zero]
    using hm

theorem character14_span : ClassFunctionSpan character14 := by
  apply ClassFunctionCompleteness.classFunctionSpan_of_card_le character14
    character14_isClassFunction character14_orthogonal
  simpa only [Nat.card_eq_fintype_card, card_shape14] using card_conjClasses_le

theorem card_conjClasses_eq : Nat.card (ConjClasses S14) = 135 := by
  apply Nat.le_antisymm card_conjClasses_le
  have h := (ClassFunctionCompleteness.descended_linearIndependent character14
    character14_isClassFunction character14_orthogonal).fintype_card_le_finrank
  simpa only [card_shape14, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card] using h

/-- The old central-averaging interface is now instantiated with actual
constructed Young characters, without any remaining character assumptions. -/
theorem character14_centralCoefficient_expansion (w : S14 → ℝ) (g : S14) :
    centralCoefficient w g = (Fintype.card S14 : ℝ)⁻¹ *
      ∑ p : Shape14, pairing w (character14 p) * character14 p g :=
  centralCoefficient_character_expansion character14 character14_isClassFunction
    character14_orthogonal character14_span w g

theorem character14_weighted_pairings_nonneg (w m : S14 → ℝ)
    (hpositive : ∀ a : S14, 0 ≤ pairing w (fun g => m (a * g * a⁻¹))) :
    0 ≤ ∑ p : Shape14, pairing w (character14 p) * pairing (character14 p) m :=
  character_weighted_pairings_nonneg character14 character14_isClassFunction
    character14_orthogonal character14_span w m hpositive

end LiebBridge.Young.YoungCharacterCompleteness
