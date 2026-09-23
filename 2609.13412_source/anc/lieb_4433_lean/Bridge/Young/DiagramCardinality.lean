import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! Cardinality of a Young diagram constructed from its row lengths.
The finite-set argument applies to every list, including lists with zero rows. -/

namespace YoungDiagram
open Function

theorem cellsOfRowLens_card (p : List ℕ) :
    (YoungDiagram.cellsOfRowLens p).card = p.sum := by
  induction p with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a p ih =>
    have hd : Disjoint (({0} : Finset ℕ) ×ˢ Finset.range a)
        ((YoungDiagram.cellsOfRowLens p).map
          (Embedding.prodMap ⟨_, Nat.succ_injective⟩ (Embedding.refl ℕ))) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hx0 : x.1 = 0 := by simpa using (Finset.mem_product.mp hx).1
      obtain ⟨y, _, heq⟩ := Finset.mem_map.mp hy
      have heq0 := congrArg Prod.fst heq
      change y.1 + 1 = x.1 at heq0
      omega
    simp only [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint hd,
      Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul,
      Finset.card_map, List.sum_cons, ih]

@[simp]
theorem ofRowLens_card (p : List ℕ) (hp : p.Sorted (· ≥ ·)) :
    (YoungDiagram.ofRowLens p hp).card = p.sum :=
  cellsOfRowLens_card p

@[simp]
theorem rowLens_sum_card (d : YoungDiagram) : d.rowLens.sum = d.card := by
  rw [← ofRowLens_card d.rowLens (rowLens_sorted d), ofRowLens_to_rowLens_eq_self]

end YoungDiagram
