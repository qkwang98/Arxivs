import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators
import Mathlib.GroupTheory.Perm.Basic

/-!
Finite-coordinate tensor and Gram realization over the complex numbers.
All index types are finite. No invertibility or rank hypothesis is used.
-/

open scoped BigOperators Matrix ComplexOrder

namespace LiebBridge

noncomputable section

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I]

/-- The coordinate model of the tensor product with one factor per `I`. -/
abbrev Tensor (I D : Type*) := (I → D) → ℂ

/-- Pure tensor with factors `v i`. -/
def pureTensor (v : I → D → ℂ) : Tensor I D := fun c => ∏ i, v i (c i)

/-- The finite-dimensional complex inner product, conjugate-linear on the left. -/
def tensorInner (x y : Tensor I D) : ℂ := ∑ c, star (x c) * y c

/-- Permute tensor positions. This convention is a left action. -/
def tensorPerm (σ : Equiv.Perm I) (x : Tensor I D) : Tensor I D :=
  fun c => x (c ∘ σ)

omit [Fintype I] [Fintype D] [DecidableEq I] in
theorem tensorPerm_one (x : Tensor I D) : tensorPerm 1 x = x := rfl

omit [Fintype I] [Fintype D] [DecidableEq I] in
theorem tensorPerm_mul (σ τ : Equiv.Perm I) (x : Tensor I D) :
    tensorPerm (σ * τ) x = tensorPerm σ (tensorPerm τ x) := rfl

/-- The coordinate reindexing induced by a position permutation. -/
def tensorCoordinatePerm (σ : Equiv.Perm I) : (I → D) ≃ (I → D) where
  toFun c := c ∘ σ
  invFun c := c ∘ (σ⁻¹ : Equiv.Perm I)
  left_inv c := by ext i; simp
  right_inv c := by ext i; simp

/-- Tensor position permutations are unitary for the concrete inner product. -/
theorem tensorInner_perm (σ : Equiv.Perm I) (x y : Tensor I D) :
    tensorInner (tensorPerm σ x) (tensorPerm σ y) = tensorInner x y := by
  classical
  exact Equiv.sum_comp (tensorCoordinatePerm σ) (fun c => star (x c) * y c)

theorem tensorInner_perm_left (σ : Equiv.Perm I) (x y : Tensor I D) :
    tensorInner (tensorPerm σ x) y = tensorInner x (tensorPerm σ⁻¹ y) := by
  have h := tensorInner_perm σ x (tensorPerm σ⁻¹ y)
  simpa only [← tensorPerm_mul, mul_inv_cancel, tensorPerm_one] using h

/-- Gram matrix of an arbitrary finite family of complex vectors. -/
def gramMatrix (v : I → D → ℂ) : Matrix I I ℂ :=
  fun i j => ∑ a, star (v i a) * v j a

theorem tensorInner_pureTensor (v w : I → D → ℂ) :
    tensorInner (pureTensor v) (pureTensor w) =
      ∏ i, ∑ a, star (v i a) * w i a := by
  classical
  simp only [tensorInner, pureTensor, star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : I) (a : D) => star (v i a) * w i a)).symm

omit [Fintype D] [DecidableEq I] in
theorem tensorPerm_pureTensor (σ : Equiv.Perm I) (v : I → D → ℂ) :
    tensorPerm σ (pureTensor v) = pureTensor (fun i => v (σ⁻¹ i)) := by
  classical
  funext c
  change (∏ i, v i (c (σ i))) = ∏ i, v (σ⁻¹ i) (c i)
  simpa using (Equiv.prod_comp σ (fun i => v (σ⁻¹ i) (c i)))

/-- The exact Gram monomial, fixing the inverse convention explicitly. -/
theorem tensorInner_perm_pureTensor (σ : Equiv.Perm I) (v : I → D → ℂ) :
    tensorInner (pureTensor v) (tensorPerm σ (pureTensor v)) =
      ∏ i, gramMatrix v i (σ⁻¹ i) := by
  rw [tensorPerm_pureTensor, tensorInner_pureTensor]
  rfl

omit [DecidableEq I] in
/-- Every complex Hermitian PSD matrix has a Gram realization in the same
dimension. Mathlib's factorization theorem includes singular matrices. -/
theorem exists_gram_of_posSemidef (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    ∃ v : I → I → ℂ, A = gramMatrix v := by
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hA
  refine ⟨fun i a => B a i, ?_⟩
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, gramMatrix] using hB

end
end LiebBridge
