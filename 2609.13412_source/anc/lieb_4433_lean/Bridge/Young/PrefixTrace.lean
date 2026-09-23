import Bridge.Young.PrefixProjector
import Bridge.Young.YoungCharacter

/-! Trace on the actual selected prefix block, and the exact inner-tableau
multiplicity. This is a finite trace theorem without a positivity hypothesis. -/

noncomputable section
namespace LiebBridge.Young.PrefixTrace

open scoped BigOperators Classical
open BranchingBasis PrefixDecomposition PrefixProjector

variable {eta nu : YoungDiagram} {m n : ℕ}

local instance : Fintype (SkewStandardTableau eta nu) := Fintype.ofFinite _

theorem initial_eq_iff_hasPrefix (h : eta ≤ nu) (t : StandardTableau nu) :
    initialDiagram t eta.card = eta ↔ HasPrefix eta t :=
  YoungDiagram.ext_iff.trans (hasPrefix_iff_initialCells h t).symm

theorem sum_indicator_subtype {X : Type*} [Fintype X] (p : X → Prop) (f : X → ℂ) :
    (∑ x : X, if p x then f x else 0) = ∑ x : {x // p x}, f x.val := by
  have h := (Equiv.sum_comp (Equiv.sumCompl p) (fun x => if p x then f x else 0)).symm
  simp only [Fintype.sum_sum_type, Equiv.sumCompl_apply_inl,
    Equiv.sumCompl_apply_inr] at h
  have hp : (∑ x : {x // p x}, if p x.val then f x.val else 0) =
      ∑ x : {x // p x}, f x.val := by
    apply Finset.sum_congr rfl
    intro x _
    rw [if_pos x.property]
  have hn : (∑ x : {x // ¬ p x}, if p x.val then f x.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg x.property]
  simpa only [hp, hn, add_zero] using h

/-- Trace against the actual embedded character projector is the trace over
the genuine prefix basis, reindexed by the proved inner/skew equivalence. -/
theorem trace_projector_mul (h : eta ≤ nu) (hη : eta.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) (T : Module.End ℂ (StandardTableau nu → ℂ)) :
    LinearMap.trace ℂ (StandardTableau nu → ℂ) (projector hη hν hm * T) =
      ∑ a : StandardTableau eta, ∑ s : SkewStandardTableau eta nu,
        T (Pi.single (glueTableau h a s).val 1) (glueTableau h a s).val := by
  rw [projector_eq_initialSelector, YoungCharacter.trace_eq_sum_coordinates]
  simp only [Module.End.mul_apply, initialSelector, DiagonalIrreducibility.diagonal_apply,
    ← hη, initial_eq_iff_hasPrefix h, ite_mul, one_mul, zero_mul]
  rw [sum_indicator_subtype]
  have he := (Equiv.sum_comp (prefixEquiv h).symm
    (fun t : PrefixTableau eta nu => T (Pi.single t.val 1) t.val)).symm
  simpa only [Fintype.sum_prod_type, prefixEquiv, Equiv.coe_fn_symm_mk] using he

/-- If the diagonal is independent of the inner tableau, its multiplicity is
exactly the actual dimension f^eta. -/
theorem trace_projector_mul_factor (h : eta ≤ nu)
    (hη : eta.card = m+1) (hν : nu.card = n+1) (hm : m+1 ≤ n+1)
    (T : Module.End ℂ (StandardTableau nu → ℂ)) (f : SkewStandardTableau eta nu → ℂ)
    (hdiag : ∀ a s, T (Pi.single (glueTableau h a s).val 1)
      (glueTableau h a s).val = f s) :
    LinearMap.trace ℂ (StandardTableau nu → ℂ) (projector hη hν hm * T) =
      (YoungProjectors.degree eta : ℂ) * ∑ s : SkewStandardTableau eta nu, f s := by
  rw [trace_projector_mul h hη hν hm]
  simp only [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, YoungProjectors.degree]

/-- A shape that does not embed in the ambient diagram has zero prefix projector. -/
theorem projector_eq_zero_of_not_le (hη : eta.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) (hne : ¬ eta ≤ nu) : projector hη hν hm = 0 := by
  rw [projector_eq_initialSelector]
  apply LinearMap.ext
  intro v
  funext t
  have ht : initialDiagram t (m+1) ≠ eta := by
    intro he
    exact hne (he ▸ initialDiagram_le t (m+1))
  simp [initialSelector, DiagonalIrreducibility.diagonal_apply, ht]

end LiebBridge.Young.PrefixTrace
