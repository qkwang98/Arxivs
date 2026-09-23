import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.ConjTranspose
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators Matrix Kronecker

namespace LiebBridge

variable {O L : Type*} [Fintype O] [Fintype L]

/-- The elementary tensor across the `(O,L) | R` bipartition. -/
def splitTensor (a : O × L → ℂ) (b : L → ℂ) : (O × L) × L → ℂ :=
  fun p => a p.1 * b p.2

/-- Swap the two identically indexed outside blocks. -/
def pairSwap (v : (O × L) × L → ℂ) : (O × L) × L → ℂ :=
  fun p => v ((p.1.1, p.2), p.1.2)

/-- Contract the middle block against the vector on the last block. -/
def contraction (a : O × L → ℂ) (b : L → ℂ) : O → ℂ :=
  fun o => ∑ l, star (b l) * a (o, l)

/-- Direct contraction identity for the swap expectation on a split tensor. -/
theorem pairSwap_expectation_eq (a : O × L → ℂ) (b : L → ℂ) :
    dotProduct (star (splitTensor a b)) (pairSwap (splitTensor a b)) =
      ∑ o, star (contraction a b o) * contraction a b o := by
  classical
  simp only [dotProduct, splitTensor, pairSwap, contraction, Pi.star_apply,
    Fintype.sum_prod_type, star_mul, star_sum, star_star,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- The swap is nonnegative on every tensor split across the indicated cut. -/
theorem pairSwap_expectation_nonneg (a : O × L → ℂ) (b : L → ℂ) :
    0 ≤ (dotProduct (star (splitTensor a b)) (pairSwap (splitTensor a b))).re := by
  rw [pairSwap_expectation_eq]
  simp only [Complex.re_sum]
  apply Finset.sum_nonneg
  intro o ho
  change 0 ≤ (star (contraction a b o) * contraction a b o).re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    using Complex.normSq_nonneg (contraction a b o)

/-- Local matrices preserve the split form; no projector assumptions are needed. -/
theorem kronecker_mulVec_split (Q : Matrix (O × L) (O × L) ℂ)
    (B : Matrix L L ℂ) (a : O × L → ℂ) (b : L → ℂ) :
    (Q ⊗ₖ B) *ᵥ splitTensor a b = splitTensor (Q *ᵥ a) (B *ᵥ b) := by
  classical
  funext p
  rcases p with ⟨p, r⟩
  simp only [Matrix.mulVec, dotProduct, splitTensor, Fintype.sum_prod_type,
    Matrix.kronecker_apply]
  rw [Finset.sum_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o ho
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Moving a matrix across the finite complex inner product takes its adjoint. -/
theorem dotProduct_adjoint_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) (x : J → ℂ) (y : I → ℂ) :
    dotProduct (star x) (Mᴴ *ᵥ y) = dotProduct (star (M *ᵥ x)) y := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- A locally filtered swap is nonnegative on split tensors. -/
theorem filtered_pairSwap_nonneg (Q : Matrix (O × L) (O × L) ℂ)
    (B : Matrix L L ℂ) (a : O × L → ℂ) (b : L → ℂ) :
    0 ≤ (dotProduct (star (splitTensor a b))
      ((Q ⊗ₖ B)ᴴ *ᵥ pairSwap ((Q ⊗ₖ B) *ᵥ splitTensor a b))).re := by
  rw [dotProduct_adjoint_mulVec, kronecker_mulVec_split]
  exact pairSwap_expectation_nonneg _ _

/-- Entrywise realization of the block swap as an actual matrix. -/
noncomputable def pairSwapMatrix : Matrix ((O × L) × L) ((O × L) × L) ℂ :=
  by
    classical
    exact fun i j => if j = ((i.1.1, i.2), i.1.2) then 1 else 0

@[simp]
theorem pairSwapMatrix_mulVec (v : (O × L) × L → ℂ) :
    pairSwapMatrix *ᵥ v = pairSwap v := by
  classical
  funext i
  simp [pairSwapMatrix, Matrix.mulVec, dotProduct, pairSwap]

/-- Matrix form of the filtered-swap witness positivity. -/
theorem local_swap_sandwich_nonneg (Q : Matrix (O × L) (O × L) ℂ)
    (B : Matrix L L ℂ) (a : O × L → ℂ) (b : L → ℂ) :
    0 ≤ (dotProduct (star (splitTensor a b))
      (((Q ⊗ₖ B)ᴴ * pairSwapMatrix * (Q ⊗ₖ B)) *ᵥ splitTensor a b)).re := by
  simp only [← Matrix.mulVec_mulVec, pairSwapMatrix_mulVec]
  exact filtered_pairSwap_nonneg Q B a b

/-- Pure matrix algebra behind the witness: the two copies of `P` collapse. -/
theorem witness_eq_adjoint_sandwich {I : Type*} [Fintype I]
    (P Q B S : Matrix I I ℂ)
    (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hB : Bᴴ = B)
    (hPid : P * P = P) (hPS : P * S = S * P) :
    Q * B * P * S * B * Q = (P * B * Q)ᴴ * S * (P * B * Q) := by
  have hPSP : P * S * P = P * S := by
    calc
      P * S * P = P * (S * P) := mul_assoc _ _ _
      _ = P * (P * S) := by rw [← hPS]
      _ = P * S := by rw [← mul_assoc, hPid]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hQ, hB]
  calc
    Q * B * P * S * B * Q = Q * B * (P * S) * B * Q := by
      simp only [mul_assoc]
    _ = Q * B * (P * S * P) * B * Q := by rw [hPSP]
    _ = Q * (B * P) * S * (P * B * Q) := by simp only [mul_assoc]

/-- The tensor-local filter needed after the projector algebra. -/
theorem projected_local_swap_nonneg [DecidableEq L] (P : Matrix O O ℂ)
    (Q : Matrix (O × L) (O × L) ℂ) (B : Matrix L L ℂ)
    (a : O × L → ℂ) (b : L → ℂ) :
    0 ≤ (dotProduct (star (splitTensor a b))
      (((((P ⊗ₖ (1 : Matrix L L ℂ)) * Q) ⊗ₖ B)ᴴ * pairSwapMatrix *
        (((P ⊗ₖ (1 : Matrix L L ℂ)) * Q) ⊗ₖ B)) *ᵥ splitTensor a b)).re := by
  classical
  exact local_swap_sandwich_nonneg _ _ _ _

/-- Adjoint of a local tensor-product matrix. -/
theorem conjTranspose_kronecker {I J : Type*}
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply, star_mul]
  exact mul_comm _ _

/-- Left multiplication by the swap permutes the row index. -/
theorem pairSwapMatrix_mul_apply (M : Matrix ((O × L) × L) ((O × L) × L) ℂ)
    (i j : (O × L) × L) :
    (pairSwapMatrix (O := O) (L := L) * M) i j = M ((i.1.1, i.2), i.1.2) j := by
  classical
  simp [Matrix.mul_apply, pairSwapMatrix]

/-- Right multiplication by the swap permutes the column index. -/
theorem mul_pairSwapMatrix_apply (M : Matrix ((O × L) × L) ((O × L) × L) ℂ)
    (i j : (O × L) × L) :
    (M * pairSwapMatrix (O := O) (L := L)) i j = M i ((j.1.1, j.2), j.1.2) := by
  classical
  have heq (k : (O × L) × L) :
      j = ((k.1.1, k.2), k.1.2) ↔ k = ((j.1.1, j.2), j.1.2) := by
    constructor
    · intro h
      have h' := congrArg (fun p : (O × L) × L => ((p.1.1, p.2), p.1.2)) h
      simpa only [Prod.eta] using h'.symm
    · intro h
      have h' := congrArg (fun p : (O × L) × L => ((p.1.1, p.2), p.1.2)) h
      simpa only [Prod.eta] using h'.symm
  simp only [Matrix.mul_apply, pairSwapMatrix, mul_ite, mul_one, mul_zero, heq]
  simp

/-- An operator supported on `O` commutes with the swap of the two outside blocks. -/
theorem outside_lift_commutes_swap [DecidableEq L] (P : Matrix O O ℂ) :
    (((P ⊗ₖ (1 : Matrix L L ℂ)) ⊗ₖ (1 : Matrix L L ℂ)) * pairSwapMatrix) =
      pairSwapMatrix * ((P ⊗ₖ (1 : Matrix L L ℂ)) ⊗ₖ (1 : Matrix L L ℂ)) := by
  classical
  ext ⟨⟨o, l⟩, r⟩ ⟨⟨p, s⟩, t⟩
  rw [mul_pairSwapMatrix_apply, pairSwapMatrix_mul_apply]
  simp only [Matrix.kronecker_apply]
  ring

/-- Extend an operator on the untouched block to all three blocks. -/
def outsideLift [DecidableEq L] (P : Matrix O O ℂ) :
    Matrix ((O × L) × L) ((O × L) × L) ℂ :=
  (P ⊗ₖ (1 : Matrix L L ℂ)) ⊗ₖ (1 : Matrix L L ℂ)

/-- Extend an operator on the first two blocks. -/
def leftLift [DecidableEq L] (Q : Matrix (O × L) (O × L) ℂ) :
    Matrix ((O × L) × L) ((O × L) × L) ℂ :=
  Q ⊗ₖ (1 : Matrix L L ℂ)

/-- Extend an operator on the last block. -/
def rightLift [DecidableEq O] [DecidableEq L] (B : Matrix L L ℂ) :
    Matrix ((O × L) × L) ((O × L) × L) ℂ :=
  (1 : Matrix (O × L) (O × L) ℂ) ⊗ₖ B

/-- The exact witness `Q B P swap B Q`, with each operator explicitly localized. -/
noncomputable def projectedSwapWitness [DecidableEq O] [DecidableEq L]
    (P : Matrix O O ℂ) (Q : Matrix (O × L) (O × L) ℂ) (B : Matrix L L ℂ) :
    Matrix ((O × L) × L) ((O × L) × L) ℂ :=
  leftLift Q * rightLift B * outsideLift (L := L) P * pairSwapMatrix * rightLift B * leftLift Q

/-- Universally nonnegative expectation of the concrete localized witness.

`P` is an orthogonal projector, and `Q` and `B` are Hermitian local filters.
In particular this covers the nested central projectors and the symmetric or
alternating pair projector. No witness-positivity assumption is present, and
no commutation of `P` with `Q` is required for this stronger version. -/
theorem projectedSwapWitness_nonneg [DecidableEq O] [DecidableEq L]
    (P : Matrix O O ℂ) (Q : Matrix (O × L) (O × L) ℂ) (B : Matrix L L ℂ)
    (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hB : Bᴴ = B) (hPid : P * P = P)
    (a : O × L → ℂ) (b : L → ℂ) :
    0 ≤ (dotProduct (star (splitTensor a b))
      (projectedSwapWitness P Q B *ᵥ splitTensor a b)).re := by
  classical
  have hPL : (outsideLift (L := L) P)ᴴ = outsideLift (L := L) P := by
    simp only [outsideLift, conjTranspose_kronecker, Matrix.conjTranspose_one, hP]
  have hQL : (leftLift Q)ᴴ = leftLift Q := by
    simp only [leftLift, conjTranspose_kronecker, Matrix.conjTranspose_one, hQ]
  have hBL : (rightLift (O := O) B)ᴴ = rightLift (O := O) B := by
    simp only [rightLift, conjTranspose_kronecker, Matrix.conjTranspose_one, hB]
  have hPLid : outsideLift (L := L) P * outsideLift (L := L) P = outsideLift (L := L) P := by
    simp only [outsideLift, ← Matrix.mul_kronecker_mul, mul_one, hPid]
  have hPLS : outsideLift (L := L) P * pairSwapMatrix = pairSwapMatrix * outsideLift (L := L) P :=
    outside_lift_commutes_swap P
  have hW := witness_eq_adjoint_sandwich (outsideLift (L := L) P) (leftLift Q)
    (rightLift B) pairSwapMatrix hPL hQL hBL hPLid hPLS
  have hK : outsideLift (L := L) P * rightLift B * leftLift Q =
      ((P ⊗ₖ (1 : Matrix L L ℂ)) * Q) ⊗ₖ B := by
    simp only [outsideLift, rightLift, leftLift, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul]
  unfold projectedSwapWitness
  rw [hW, hK]
  exact projected_local_swap_nonneg P Q B a b

end LiebBridge
