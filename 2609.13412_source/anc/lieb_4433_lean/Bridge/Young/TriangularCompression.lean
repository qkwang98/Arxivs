import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Restriction of matrices along a two-step invariant flag is multiplicative.
The retained indices are column-valid and row-valid. The result uses concrete
zero entries, not a representation-theoretic identification assumption. -/

namespace LiebBridge.Young.TriangularCompression
open scoped BigOperators Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Semiring K]

/-- The column-valid span is invariant, and its row-invalid span is invariant.
Rows are targets and columns are sources. -/
def PreservesFlag (C R : ι → Prop) (M : Matrix ι ι K) : Prop :=
  (∀ a b, C b → ¬ C a → M a b = 0) ∧
  (∀ a b, C a → R a → C b → ¬ R b → M a b = 0)

abbrev Retained (C R : ι → Prop) := {i // C i ∧ R i}

def compress (C R : ι → Prop) (M : Matrix ι ι K) :
    Matrix (Retained C R) (Retained C R) K := fun a b => M a.val b.val

omit [DecidableEq ι] in
theorem preservesFlag_mul (C R : ι → Prop) {M N : Matrix ι ι K}
    (hM : PreservesFlag C R M) (hN : PreservesFlag C R N) :
    PreservesFlag C R (M * N) := by
  classical
  constructor
  · intro a b hb ha
    apply Finset.sum_eq_zero
    intro k hk
    change M a k * N k b = 0
    by_cases hC : C k
    · rw [hM.1 a k hC ha, zero_mul]
    · rw [hN.1 k b hb hC, mul_zero]
  · intro a b haC haR hbC hbR
    apply Finset.sum_eq_zero
    intro k hk
    change M a k * N k b = 0
    by_cases hC : C k
    · by_cases hR : R k
      · rw [hN.2 k b hC hR hbC hbR, mul_zero]
      · rw [hM.2 a k haC haR hC hR, zero_mul]
    · rw [hN.1 k b hbC hC, mul_zero]

omit [Fintype ι] in
theorem preservesFlag_one (C R : ι → Prop) :
    PreservesFlag C R (1 : Matrix ι ι K) := by
  constructor
  · intro a b hb ha
    have hne : a ≠ b := by intro h; exact ha (h ▸ hb)
    simp [Matrix.one_apply, hne]
  · intro a b haC haR hbC hbR
    have hne : a ≠ b := by intro h; exact hbR (h ▸ haR)
    simp [Matrix.one_apply, hne]

omit [DecidableEq ι] in
theorem compress_mul (C R : ι → Prop) [DecidablePred C] [DecidablePred R]
    {M N : Matrix ι ι K} (hM : PreservesFlag C R M) (hN : PreservesFlag C R N) :
    compress C R (M * N) = compress C R M * compress C R N := by
  ext a b
  change (∑ k, M a.val k * N k b.val) =
    ∑ k : Retained C R, M a.val k.val * N k.val b.val
  apply Finset.sum_congr_set {i | C i ∧ R i}
  · intro k hk
    rfl
  · intro k hk
    by_cases hC : C k
    · have hR : ¬ R k := fun hr => hk ⟨hC, hr⟩
      rw [hM.2 a.val k a.property.1 a.property.2 hC hR, zero_mul]
    · rw [hN.1 k b.val b.property.1 hC, mul_zero]

omit [Fintype ι] in
theorem compress_one (C R : ι → Prop) [DecidablePred C] [DecidablePred R] :
    compress C R (1 : Matrix ι ι K) = 1 := by
  ext a b
  simp [compress, Matrix.one_apply, Subtype.ext_iff]

theorem compress_involution (C R : ι → Prop) [DecidablePred C] [DecidablePred R]
    {M : Matrix ι ι K} (hM : PreservesFlag C R M) (hsq : M * M = 1) :
    compress C R M * compress C R M = 1 := by
  rw [← compress_mul C R hM hM, hsq, compress_one]

omit [DecidableEq ι] in
/-- Any braid relation is inherited by the quotient's retained-index matrices. -/
theorem compress_braid (C R : ι → Prop) [DecidablePred C] [DecidablePred R]
    {M N : Matrix ι ι K} (hM : PreservesFlag C R M) (hN : PreservesFlag C R N)
    (hbraid : M * N * M = N * M * N) :
    compress C R M * compress C R N * compress C R M =
      compress C R N * compress C R M * compress C R N := by
  have h := congrArg (compress C R) hbraid
  rw [compress_mul C R (preservesFlag_mul C R hM hN) hM,
    compress_mul C R (preservesFlag_mul C R hN hM) hN,
    compress_mul C R hM hN, compress_mul C R hN hM] at h
  exact h

end LiebBridge.Young.TriangularCompression
