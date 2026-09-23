import Bridge.Young.YoungRepresentation
import Bridge.Young.DiagonalIrreducibility
import Mathlib.Data.Complex.Basic

/-! Extend the verified rational tableau representation by entrywise scalar
extension. The ring homomorphism preserves all proved operator identities. -/

noncomputable section
namespace LiebBridge.Young.ScalarExtension

open scoped BigOperators Matrix
open StandardTableau

variable {B : Type*} [Fintype B] [DecidableEq B]
variable (K : Type*) [Field K] [CharZero K]

/-- Entrywise scalar extension of a finite coordinate endomorphism. -/
def extend : Module.End ℚ (B → ℚ) →+* Module.End K (B → K) :=
  (Matrix.toLinAlgEquiv').toRingHom.comp
    (((algebraMap ℚ K).mapMatrix).comp (LinearMap.toMatrixAlgEquiv').toRingHom)

theorem extend_apply (T : Module.End ℚ (B → ℚ)) (v : B → K) (b : B) :
    extend K T v b = ∑ a : B, (T (Pi.single a 1) b : K) * v a := by
  change (((LinearMap.toMatrixAlgEquiv' T).map (algebraMap ℚ K)) *ᵥ v) b = _
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
    LinearMap.toMatrixAlgEquiv'_apply]
  change (∑ a, (T (fun j' => if j' = a then 1 else 0) b : K) * v a) = _
  apply Finset.sum_congr rfl
  intro a ha
  have he : (fun j' : B => if j' = a then (1 : ℚ) else 0) = Pi.single a 1 := by
    funext j'
    simp [Pi.single_apply, eq_comm]
  rw [he]

theorem extend_basis_coefficient (T : Module.End ℚ (B → ℚ)) (a b : B) :
    extend K T (Pi.single a 1) b = (T (Pi.single a 1) b : K) := by
  rw [extend_apply]
  simp [Pi.single_apply, eq_comm]

theorem extend_diagonal (c : B → ℚ) :
    extend K (DiagonalIrreducibility.diagonal c) =
      DiagonalIrreducibility.diagonal (fun b => (c b : K)) := by
  apply LinearMap.ext
  intro v
  funext b
  rw [extend_apply]
  simp [DiagonalIrreducibility.diagonal_apply, Pi.single_apply, eq_comm, apply_ite]

variable {d : YoungDiagram} {n : ℕ}

local instance : DecidableEq (StandardTableau d) := Classical.decEq _

/-- The actual Young representation over any characteristic-zero field,
including the complex field used for the Hermitian PSD theorem. -/
def representation (hcard : d.card = n + 1) :
    Representation K (Equiv.Perm (Fin (n+1))) (StandardTableau d → K) := by
  classical
  exact (extend K).toMonoidHom.comp (YoungRepresentation.representation hcard)

theorem representation_adjacent (hcard : d.card = n + 1) (i : Fin n) :
    representation K hcard (Equiv.swap i.castSucc i.succ) =
      extend K (YoungRepresentation.adjacentOperator hcard i) := by
  classical
  change extend K (YoungRepresentation.representation hcard _) = _
  rw [YoungRepresentation.representation_adjacent]

theorem contentOperator_eq_diagonal (i : Fin d.card) :
    contentOperator i = DiagonalIrreducibility.diagonal (fun t => t.rationalContent i) := rfl

/-- The proven content recurrence survives scalar extension exactly. -/
theorem extended_content_recurrence (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    extend K (contentOperator j) =
      extend K (generator i j hij) * extend K (contentOperator i) *
        extend K (generator i j hij) + extend K (generator i j hij) := by
  classical
  rw [← map_mul, ← map_mul, ← map_add, content_recurrence]

end LiebBridge.Young.ScalarExtension
