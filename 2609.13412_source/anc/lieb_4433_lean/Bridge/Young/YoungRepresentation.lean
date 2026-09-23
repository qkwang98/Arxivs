import Bridge.Young.StandardCompression
import Bridge.Young.CoxeterExtension
import Mathlib.RepresentationTheory.Basic

/-! The actual rational symmetric-group representation determined by the
proved seminormal operators on genuine standard Young tableaux. -/

noncomputable section
namespace LiebBridge.Young.YoungRepresentation

open StandardTableau

def leftIndex {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1) (i : Fin n) :
    Fin d.card := ⟨i.val, by omega⟩

def rightIndex {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1) (i : Fin n) :
    Fin d.card := ⟨i.val + 1, by omega⟩

@[simp] theorem leftIndex_val {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1)
    (i : Fin n) : (leftIndex hcard i).val = i.val := rfl

@[simp] theorem rightIndex_val {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1)
    (i : Fin n) : (rightIndex hcard i).val = i.val + 1 := rfl

def adjacentOperator {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1) (i : Fin n) :
    Module.End ℚ (StandardTableau d → ℚ) :=
  generator (leftIndex hcard i) (rightIndex hcard i) rfl

theorem adjacent_relations {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1) :
    Bridge.Young.CoxeterExtension.Relations n
      (Bridge.Young.CoxeterExtension.extendFamily (adjacentOperator hcard)) := by
  constructor
  · intro i hi
    simp only [Bridge.Young.CoxeterExtension.extendFamily, dif_pos hi, adjacentOperator]
    exact generator_square _ _ _
  · intro i j hi hj hij
    simp only [Bridge.Young.CoxeterExtension.extendFamily, dif_pos hi, dif_pos hj,
      adjacentOperator]
    apply generator_commute
    all_goals
      intro h
      have hh := congrArg Fin.val h
      simp only [leftIndex_val, rightIndex_val, Fin.val_mk] at hh
      omega
  · intro i hi
    have hi' : i < n := by omega
    simp only [Bridge.Young.CoxeterExtension.extendFamily, dif_pos hi, dif_pos hi',
      adjacentOperator]
    let a : Fin d.card := ⟨i, by omega⟩
    let b : Fin d.card := ⟨i+1, by omega⟩
    let c : Fin d.card := ⟨i+2, by omega⟩
    change generator a b rfl * generator b c rfl * generator a b rfl =
      generator b c rfl * generator a b rfl * generator b c rfl
    exact generator_braid a b c rfl rfl

/-- A representation of the actual permutation group, constructed from the
structurally proved square, distant-commutation, and braid relations. -/
def representation {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1) :
    Representation ℚ (Equiv.Perm (Fin (n+1))) (StandardTableau d → ℚ) :=
  Bridge.Young.CoxeterExtension.extension (adjacentOperator hcard) (adjacent_relations hcard)

@[simp] theorem representation_adjacent {d : YoungDiagram} {n : ℕ}
    (hcard : d.card = n + 1) (i : Fin n) :
    representation hcard (Equiv.swap i.castSucc i.succ) = adjacentOperator hcard i :=
  Bridge.Young.CoxeterExtension.extension_adjacent _ _ i

/-- The action of an adjacent permutation is exactly the original row-form
seminormal operator, with no trace or irreducibility assumption. -/
theorem representation_adjacent_apply {d : YoungDiagram} {n : ℕ}
    (hcard : d.card = n + 1) (i : Fin n) (v : StandardTableau d → ℚ) (t : StandardTableau d) :
    representation hcard (Equiv.swap i.castSucc i.succ) v t =
      (t.axial (leftIndex hcard i) (rightIndex hcard i))⁻¹ * v t +
        if ¬ t.entry (leftIndex hcard i) ≤ t.entry (rightIndex hcard i) then
          (1 - (t.axial (leftIndex hcard i) (rightIndex hcard i))⁻¹) *
            v (t.adjacentSwap (leftIndex hcard i) (rightIndex hcard i) rfl)
        else 0 := by
  rw [representation_adjacent]
  rfl

theorem representation_unique {d : YoungDiagram} {n : ℕ} (hcard : d.card = n + 1)
    (ρ : Representation ℚ (Equiv.Perm (Fin (n+1))) (StandardTableau d → ℚ))
    (hρ : ∀ i : Fin n, ρ (Equiv.swap i.castSucc i.succ) = adjacentOperator hcard i) :
    ρ = representation hcard := by
  apply (Bridge.Young.CoxeterExtension.symmetricSystem n).ext_simple
  intro i
  rw [Bridge.Young.CoxeterExtension.symmetricSystem_simple]
  exact (hρ i).trans (representation_adjacent hcard i).symm

end LiebBridge.Young.YoungRepresentation
