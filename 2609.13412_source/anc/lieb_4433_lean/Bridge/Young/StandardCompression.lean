import Bridge.Young.AmbientBraid
import Bridge.Young.Seminormal

/-! Identification of the concrete flag quotient basis with genuine standard
tableaux, including the source-column to target-row coefficient conversion. -/

noncomputable section
namespace LiebBridge.Young
namespace StandardCompression
open scoped Matrix
attribute [local instance] Classical.propDecidable

def standardEquiv (d : YoungDiagram) :
    StandardTableau d ≃ TriangularCompression.Retained (@ColumnIncreasing d) RowIncreasing where
  toFun t := ⟨t.number, (strictMono_iff_flags t.number).mp t.increasing⟩
  invFun e := ⟨e.val, (strictMono_iff_flags e.val).mpr e.property⟩
  left_inv t := by apply StandardTableau.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

@[simp] theorem standardEquiv_val {d : YoungDiagram} (t : StandardTableau d) :
    (standardEquiv d t).val = t.number := rfl

theorem numberingSwap_involutive {d : YoungDiagram} (e : Numbering d) (i j : Fin d.card) :
    numberingSwap (numberingSwap e i j) i j = e := by
  ext x
  simp [numberingSwap]

theorem numberingSwap_standard_iff {d : YoungDiagram} (s t : StandardTableau d)
    (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    s.number = numberingSwap t.number i j ↔
      ¬ t.entry i ≤ t.entry j ∧ s = t.adjacentSwap i j hij := by
  constructor
  · intro h
    have hs : ¬ t.entry i ≤ t.entry j := by
      intro hle
      have hh := s.number_le _ _ hle
      rw [h] at hh
      simp [numberingSwap, StandardTableau.entry] at hh
      omega
    refine ⟨hs, ?_⟩
    apply StandardTableau.ext
    rw [StandardTableau.adjacentSwap_of_allowed _ _ _ _ hs]
    exact h
  · rintro ⟨hs, rfl⟩
    rw [StandardTableau.adjacentSwap_of_allowed _ _ _ _ hs]
    rfl

theorem numberingSwap_standard_row_iff {d : YoungDiagram} (s t : StandardTableau d)
    (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    s.number = numberingSwap t.number i j ↔
      ¬ s.entry i ≤ s.entry j ∧ t = s.adjacentSwap i j hij := by
  have he : s.number = numberingSwap t.number i j ↔
      t.number = numberingSwap s.number i j := by
    constructor <;> intro h
    · rw [h, numberingSwap_involutive]
    · rw [h, numberingSwap_involutive]
  rw [he, numberingSwap_standard_iff]

theorem numberingGap_eq_axial {d : YoungDiagram} (t : StandardTableau d) (i j : Fin d.card) :
    numberingGap t.number i j = t.axial i j := rfl

/-- Equality with the actual coordinate matrix of the existing row-form
generator, not merely equality between two independently stored arrays. -/
theorem generatorMatrix_eq_compressedSubmatrix {d : YoungDiagram}
    (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    StandardTableau.generatorMatrix i j hij =
      (AmbientBraid.compressedMatrix i j).submatrix (standardEquiv d) (standardEquiv d) := by
  classical
  ext s t
  simp only [StandardTableau.generatorMatrix, LinearMap.toMatrix'_apply,
    StandardTableau.generator_apply, Matrix.submatrix_apply,
    AmbientBraid.compressedMatrix, TriangularCompression.compress,
    standardEquiv_val, AmbientBraid.numberingMatrix, numberingGap_eq_axial]
  have hst : s.number = t.number ↔ s = t :=
    ⟨fun h => StandardTableau.ext h, fun h => congrArg StandardTableau.number h⟩
  simp only [hst, numberingSwap_standard_row_iff s t i j hij]
  by_cases hs : ¬ s.entry i ≤ s.entry j
  · simp only [hs, if_true, true_and]
    by_cases ht : t = s.adjacentSwap i j hij
    · subst t
      rw [StandardTableau.axial_adjacentSwap _ _ _ _ hs]
      by_cases he : s = s.adjacentSwap i j hij
      · have hd := s.axial_ne_zero i j hij
        have hneg : s.axial i j = -s.axial i j := by
          simpa only [← he] using s.axial_adjacentSwap i j hij hs
        have hz : s.axial i j = 0 := by linarith only [hneg]
        exact (hd hz).elim
      · simp [he, one_div, inv_neg, sub_eq_add_neg]
    · have ht' : s.adjacentSwap i j hij ≠ t := Ne.symm ht
      simp only [if_neg ht, if_neg ht', mul_zero, add_zero]
      by_cases he : s = t
      · subst t; simp [one_div, ht]
      · simp [he, ht]
  · simp only [hs, false_and, if_false, add_zero]
    by_cases he : s = t
    · subst t; simp [one_div]
    · simp [he]

end StandardCompression

namespace StandardTableau

/-- The actual rational seminormal operators satisfy the adjacent braid. -/
theorem generator_braid {d : YoungDiagram} (i j k : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hjk : (k : ℕ) = (j : ℕ) + 1) :
    generator i j hij * generator j k hjk * generator i j hij =
      generator j k hjk * generator i j hij * generator j k hjk := by
  classical
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_mul]
  change generatorMatrix i j hij * generatorMatrix j k hjk * generatorMatrix i j hij =
    generatorMatrix j k hjk * generatorMatrix i j hij * generatorMatrix j k hjk
  rw [StandardCompression.generatorMatrix_eq_compressedSubmatrix i j hij,
    StandardCompression.generatorMatrix_eq_compressedSubmatrix j k hjk]
  simp only [Matrix.submatrix_mul_equiv]
  rw [AmbientBraid.compressed_braid i j k hij hjk]

end StandardTableau
end LiebBridge.Young
