import Bridge.Young.YoungIrreducibility
import Bridge.Young.CrossShapeSeparation

/-!
# Inequivalence of the actual Young representations

An intertwiner commutes with the recursively defined content operators. For different
shapes, each source/target tableau pair differs in some content coordinate, forcing its
intertwiner coefficient to vanish. This proves inequivalence without character labels.
-/

noncomputable section
namespace LiebBridge.Young.YoungInequivalence

open StandardTableau DiagonalIrreducibility YoungIrreducibility

variable (K : Type*) [Field K] [CharZero K]
variable {eta nu : YoungDiagram} {n : ℕ}

local instance : DecidableEq (StandardTableau eta) := Classical.decEq _

/-- Intertwining the actual group action entails intertwining every content operator. -/
theorem intertwines_contents (hη : eta.card = n+1) (hν : nu.card = n+1)
    (F : (StandardTableau eta → K) →ₗ[K] (StandardTableau nu → K))
    (hF : ∀ g x, F (ScalarExtension.representation K hη g x) =
      ScalarExtension.representation K hν g (F x)) :
    ∀ i : Fin (n+1), ∀ x,
      F (diagonal (contentTuple K hη i) x) = diagonal (contentTuple K hν i) (F x) := by
  classical
  intro i
  induction i using Fin.induction with
  | zero => simp only [contentTuple_zero, LinearMap.zero_apply, map_zero, forall_const]
  | succ i ih =>
    intro x
    rw [contentTuple_recurrence, contentTuple_recurrence]
    simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, hF, ih]

private theorem diagonal_single_one {A : Type*} [DecidableEq A]
    (c : A → K) (a : A) : diagonal c (Pi.single a 1) = c a • (Pi.single a 1 : A → K) := by
  funext b
  by_cases hb : b = a
  · subst b
    simp [diagonal_apply, Pi.single_apply]
  · simp [diagonal_apply, Pi.single_apply, hb, Ne.symm hb]

private theorem single_eq_smul_one {A : Type*} [DecidableEq A] (a : A) (x : K) :
    (Pi.single a x : A → K) = x • (Pi.single a 1 : A → K) := by
  funext b
  by_cases hb : b = a
  · subst b
    simp [Pi.single_apply]
  · simp [Pi.single_apply, hb, Ne.symm hb]

/-- Every matrix coefficient of an intertwiner between distinct shapes vanishes. -/
theorem intertwiner_coefficient_zero (hη : eta.card = n+1) (hν : nu.card = n+1)
    (hne : eta ≠ nu)
    (F : (StandardTableau eta → K) →ₗ[K] (StandardTableau nu → K))
    (hF : ∀ g x, F (ScalarExtension.representation K hη g x) =
      ScalarExtension.representation K hν g (F x))
    (t : StandardTableau eta) (u : StandardTableau nu) : F (Pi.single t 1) u = 0 := by
  classical
  obtain ⟨i,hi⟩ := CrossShapeSeparation.exists_cast_content_ne (K := K)
    (hη.trans hν.symm) hne t u
  let j : Fin (n+1) := ⟨i.val, by omega⟩
  have hne' : contentTuple K hη j t ≠ contentTuple K hν j u := hi
  have he := congrFun (intertwines_contents K hη hν F hF j (Pi.single t 1)) u
  rw [diagonal_single_one, map_smul] at he
  change contentTuple K hη j t * F (Pi.single t 1) u =
    contentTuple K hν j u * F (Pi.single t 1) u at he
  have hz : (contentTuple K hη j t - contentTuple K hν j u) * F (Pi.single t 1) u = 0 := by
    rw [sub_mul, he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne')

/-- There are no nonzero intertwiners between actual equally-sized Young representations
of different diagrams, over any characteristic-zero field. -/
theorem intertwiner_eq_zero (hη : eta.card = n+1) (hν : nu.card = n+1)
    (hne : eta ≠ nu)
    (F : (StandardTableau eta → K) →ₗ[K] (StandardTableau nu → K))
    (hF : ∀ g x, F (ScalarExtension.representation K hη g x) =
      ScalarExtension.representation K hν g (F x)) : F = 0 := by
  classical
  apply LinearMap.pi_ext
  intro t a
  change F (Pi.single t a) = 0
  have hz : F (Pi.single t 1) = 0 := funext (intertwiner_coefficient_zero K hη hν hne F hF t)
  rw [single_eq_smul_one, map_smul, hz, smul_zero]

/-- In particular, no linear equivalence can intertwine two distinct shapes. -/
theorem no_intertwining_linearEquiv (hη : eta.card = n+1) (hν : nu.card = n+1)
    (hne : eta ≠ nu)
    (F : (StandardTableau eta → K) ≃ₗ[K] (StandardTableau nu → K))
    (hF : ∀ g x, F (ScalarExtension.representation K hη g x) =
      ScalarExtension.representation K hν g (F x)) : False := by
  have hz := intertwiner_eq_zero K hη hν hne F.toLinearMap hF
  have he : F (1 : StandardTableau eta → K) = F 0 := by
    have hh := congrArg (fun L : (StandardTableau eta → K) →ₗ[K] (StandardTableau nu → K) => L 1) hz
    simpa using hh
  exact one_ne_zero (F.injective he)

end LiebBridge.Young.YoungInequivalence
