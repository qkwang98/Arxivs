import Bridge.Young.BranchingBasis
import Mathlib.Data.Fintype.Card

/-! Every standard tableau has a unique genuine Young diagram as its prefix.
This proves full coverage by the prefix blocks, including all boundary shapes. -/

namespace LiebBridge.Young.PrefixDecomposition

open BranchingBasis StandardTableau

variable {nu eta : YoungDiagram}

theorem initialCells_lower (t : StandardTableau nu) (m : ℕ) :
    IsLowerSet (initialCells t m : Set (ℕ × ℕ)) := by
  intro b a hab hb
  have hbn : b ∈ nu.cells := initialCells_subset t m hb
  have han : a ∈ nu.cells := nu.isLowerSet hab hbn
  have hb' := (mem_initialCells t m ⟨b,hbn⟩).mp hb
  apply (mem_initialCells t m ⟨a,han⟩).mpr
  have hnum := t.number_le ⟨a,han⟩ ⟨b,hbn⟩ hab
  omega

def initialDiagram (t : StandardTableau nu) (m : ℕ) : YoungDiagram :=
  ⟨initialCells t m, initialCells_lower t m⟩

theorem initialDiagram_le (t : StandardTableau nu) (m : ℕ) :
    initialDiagram t m ≤ nu := initialCells_subset t m

theorem initialDiagram_card (t : StandardTableau nu) (m : ℕ) (hm : m ≤ nu.card) :
    (initialDiagram t m).card = m := by
  classical
  change (initialCells t m).card = m
  unfold initialCells
  have hi : Function.Injective (fun i : Fin nu.card => (t.entry i).val) :=
    fun i j h => t.number.symm.injective (Subtype.ext h)
  rw [Finset.card_image_of_injective _ hi]
  simpa only [Fintype.card_subtype] using Fintype.card_fin_lt_of_le hm

theorem hasPrefix_initialDiagram (t : StandardTableau nu) (m : ℕ) (hm : m ≤ nu.card) :
    HasPrefix (initialDiagram t m) t := by
  intro b
  rw [initialDiagram_card t m hm]
  exact (mem_initialCells t m b).symm

theorem initialDiagram_eq_of_hasPrefix (h : eta ≤ nu) (t : StandardTableau nu)
    (ht : HasPrefix eta t) : initialDiagram t eta.card = eta := by
  apply YoungDiagram.ext
  exact (hasPrefix_iff_initialCells h t).mp ht

/-- No standard tableau is omitted from the prefix-block decomposition. -/
theorem exists_unique_prefix (t : StandardTableau nu) (m : ℕ) (hm : m ≤ nu.card) :
    ∃! eta : YoungDiagram, eta ≤ nu ∧ eta.card = m ∧ HasPrefix eta t := by
  refine ⟨initialDiagram t m,
    ⟨initialDiagram_le t m, initialDiagram_card t m hm, hasPrefix_initialDiagram t m hm⟩, ?_⟩
  intro eta h
  have he := initialDiagram_eq_of_hasPrefix h.1 t h.2.2
  rw [h.2.1] at he
  exact he.symm

end LiebBridge.Young.PrefixDecomposition
