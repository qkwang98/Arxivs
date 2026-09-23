import Bridge.Young.YoungRepresentation
import Bridge.Young.DiagonalIrreducibility
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Sort

/-!
# Existence of genuine standard tableaux and the initial content operator

A linear extension of the cell order gives a standard tableau of every Young diagram.
In every standard tableau the first numbered cell is the origin, so its content operator
is zero. The proved seminormal recurrence then derives content invariance from invariance
under the actual adjacent generators.
-/

namespace LiebBridge.Young

namespace TableauExistence

/-- A genuine standard tableau, obtained by linearly extending the finite cell order. -/
noncomputable def standardTableau (d : YoungDiagram) : StandardTableau d := by
  classical
  letI : Fintype (LinearExtension (Cell d)) := inferInstanceAs (Fintype (Cell d))
  have hcard : Fintype.card (LinearExtension (Cell d)) = d.card := by
    change Fintype.card (Cell d) = d.card
    simp [Cell, YoungDiagram.card]
  let e : Fin d.card ≃o LinearExtension (Cell d) := monoEquivOfFin _ hcard
  refine ⟨e.symm.toEquiv, ?_⟩
  have hlin : StrictMono (toLinearExtension : Cell d → LinearExtension (Cell d)) :=
    toLinearExtension.monotone.strictMono_of_injective (fun _ _ h => h)
  exact e.symm.strictMono.comp hlin

instance nonempty_standardTableau (d : YoungDiagram) : Nonempty (StandardTableau d) :=
  ⟨standardTableau d⟩

end TableauExistence

namespace StandardTableau

variable {d : YoungDiagram}

/-- The cell carrying label zero is the origin of the Young diagram. -/
theorem entry_of_label_zero (t : StandardTableau d) (i : Fin d.card) (hi : i.val = 0) :
    (t.entry i).val = (0,0) := by
  let b := t.entry i
  have horigin : (0,0) ∈ d.cells := d.up_left_mem (Nat.zero_le _) (Nat.zero_le _) b.property
  let a : Cell d := ⟨(0,0),horigin⟩
  have hab : a ≤ b := by
    change (0,0) ≤ b.val
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hnumber := t.number_le a b hab
  have hb : (t.number b).val = 0 := by simp [b,hi]
  have heq : t.number a = t.number b := by apply Fin.ext; omega
  have he := congrArg (fun c : Cell d => c.val) (t.number.injective heq)
  exact he.symm

theorem rationalContent_of_label_zero (t : StandardTableau d) (i : Fin d.card)
    (hi : i.val = 0) : t.rationalContent i = 0 := by
  unfold rationalContent
  rw [entry_of_label_zero t i hi]
  norm_num [boxContent]

/-- The initial diagonal content operator is actually zero. -/
theorem contentOperator_of_label_zero (i : Fin d.card) (hi : i.val = 0) :
    contentOperator i = 0 := by
  ext v t
  change t.rationalContent i * v t = 0
  rw [rationalContent_of_label_zero t i hi, zero_mul]

@[simp] theorem contentOperator_zero [NeZero d.card] :
    contentOperator (0 : Fin d.card) = 0 := contentOperator_of_label_zero _ rfl

end StandardTableau

namespace TableauExistence

open StandardTableau

/-- On the actual Young tableau module, adjacent invariance implies every content invariance. -/
theorem content_invariant_of_adjacent {d : YoungDiagram} {n : ℕ}
    (hcard : d.card = n+1) (W : Submodule ℚ (StandardTableau d → ℚ))
    (hW : ∀ i : Fin n, W ∈ (YoungRepresentation.adjacentOperator hcard i).invtSubmodule) :
    ∀ i : Fin d.card, W ∈ (contentOperator i).invtSubmodule := by
  classical
  let D : Fin (n+1) → Module.End ℚ (StandardTableau d → ℚ) :=
    fun i => contentOperator ⟨i.val, by omega⟩
  let S := YoungRepresentation.adjacentOperator hcard
  have hzero : D 0 = 0 := contentOperator_of_label_zero _ rfl
  have hrec : ∀ i : Fin n, D i.succ = S i * D i.castSucc * S i + S i := by
    intro i
    exact (content_recurrence (YoungRepresentation.leftIndex hcard i)
      (YoungRepresentation.rightIndex hcard i) rfl).symm
  have hD := DiagonalIrreducibility.invariant_of_adjacent_recurrence W D S hzero hrec hW
  intro i
  exact hD ⟨i.val, by omega⟩

/-- Every invariant submodule of the genuine Young representation is content invariant. -/
theorem content_invariant_of_representation {d : YoungDiagram} {n : ℕ}
    (hcard : d.card = n+1) (W : Submodule ℚ (StandardTableau d → ℚ))
    (hW : W ∈ (YoungRepresentation.representation hcard).invtSubmodule) :
    ∀ i : Fin d.card, W ∈ (contentOperator i).invtSubmodule := by
  apply content_invariant_of_adjacent hcard W
  intro i
  have hh := (YoungRepresentation.representation hcard).mem_invtSubmodule.mp hW
    (Equiv.swap i.castSucc i.succ)
  simpa only [YoungRepresentation.representation_adjacent] using hh

end TableauExistence

end LiebBridge.Young
