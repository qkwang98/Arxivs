import Bridge.Young.PrefixProjector
import Mathlib.Tactic

/-! Algebra of the actual embedded prefix character projectors. Disjoint
suffix swaps commute at the permutation level, before applying any representation. -/

noncomputable section
namespace LiebBridge.Young.PrefixProjectorAlgebra
open scoped BigOperators Classical
open PrefixRepresentation PrefixProjector

variable {eta mu nu : YoungDiagram} {m q n : ℕ}

theorem prefixEmbedding_fixed (hm : m+1 ≤ n+1)
    (g : Equiv.Perm (Fin (m+1))) (i : Fin (n+1)) (hi : m+1 ≤ i.val) :
    prefixEmbedding hm g i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_not_mem
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem commute_swap_of_fixed {X : Type*} [DecidableEq X]
    (g : Equiv.Perm X) (a b : X) (ha : g a = a) (hb : g b = b) :
    Commute g (Equiv.swap a b) := by
  apply Equiv.ext
  intro x
  simpa only [Equiv.Perm.mul_apply, ha, hb] using g.injective.map_swap a b x

theorem prefixEmbedding_commute_swap (hm : m+1 ≤ n+1)
    (g : Equiv.Perm (Fin (m+1))) (a b : Fin (n+1))
    (ha : m+1 ≤ a.val) (hb : m+1 ≤ b.val) :
    Commute (prefixEmbedding hm g) (Equiv.swap a b) :=
  commute_swap_of_fixed _ _ _ (prefixEmbedding_fixed hm g a ha)
    (prefixEmbedding_fixed hm g b hb)

theorem projector_idempotent (hη : eta.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) : projector hη hν hm * projector hη hν hm = projector hη hν hm := by
  rw [projector_eq_initialSelector]
  apply LinearMap.ext
  intro v
  funext t
  simp only [Module.End.mul_apply, initialSelector, DiagonalIrreducibility.diagonal_apply]
  split_ifs <;> simp

theorem projectors_commute (hη : eta.card = m+1) (hμ : mu.card = q+1)
    (hν : nu.card = n+1) (hm : m+1 ≤ n+1) (hq : q+1 ≤ n+1) :
    Commute (projector hη hν hm) (projector hμ hν hq) := by
  rw [projector_eq_initialSelector, projector_eq_initialSelector]
  apply LinearMap.ext
  intro v
  funext t
  simp only [Module.End.mul_apply, initialSelector, DiagonalIrreducibility.diagonal_apply]
  ring

/-- A suffix transposition commutes with the actual embedded character sum. -/
theorem projector_commute_swap (hη : eta.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) (a b : Fin (n+1))
    (ha : m+1 ≤ a.val) (hb : m+1 ≤ b.val) :
    Commute (projector hη hν hm)
      (ScalarExtension.representation ℂ hν (Equiv.swap a b)) := by
  change _ * _ = _ * _
  simp only [projector, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [← map_mul, ← map_mul,
    (prefixEmbedding_commute_swap hm g a b ha hb).eq]

end LiebBridge.Young.PrefixProjectorAlgebra
