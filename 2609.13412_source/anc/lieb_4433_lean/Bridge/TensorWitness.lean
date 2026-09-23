import Bridge.TensorGram
import Bridge.Contraction
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Regrouping an ordinary pure tensor into the three blocks used by the witnesses.
This connects the finite-coordinate tensor model to the direct contraction
lemma. The local operators are explicit matrices; their representation-theoretic
identification is not assumed or asserted here.
-/

open scoped BigOperators Matrix Kronecker

namespace LiebBridge
noncomputable section

variable {O L D : Type*} [Fintype O] [Fintype L] [Fintype D]
  [DecidableEq O] [DecidableEq L] [DecidableEq D]

/-- Regroup a tensor coordinate into the untouched, left, and right blocks. -/
def blockCoordinates : (((O ⊕ L) ⊕ L) → D) ≃ ((O → D) × (L → D)) × (L → D) :=
  (Equiv.sumArrowEquivProdArrow (O ⊕ L) L D).trans
    (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow O L D) (Equiv.refl _))

def regroupTensor (x : Tensor ((O ⊕ L) ⊕ L) D) :
    ((O → D) × (L → D)) × (L → D) → ℂ :=
  fun c => x (blockCoordinates.symm c)

/-- Regrouping preserves the complex inner product exactly. -/
theorem regroupTensor_inner (x y : Tensor ((O ⊕ L) ⊕ L) D) :
    dotProduct (star (regroupTensor x)) (regroupTensor y) = tensorInner x y := by
  classical
  unfold dotProduct regroupTensor tensorInner
  exact Equiv.sum_comp blockCoordinates.symm (fun c => star (x c) * y c)

def firstTwoFactors (v : ((O ⊕ L) ⊕ L) → D → ℂ) : (O → D) × (L → D) → ℂ :=
  fun c => (∏ o, v (Sum.inl (Sum.inl o)) (c.1 o)) *
    ∏ l, v (Sum.inl (Sum.inr l)) (c.2 l)

def lastFactors (v : ((O ⊕ L) ⊕ L) → D → ℂ) : (L → D) → ℂ :=
  pureTensor (fun l => v (Sum.inr l))

/-- A pure tensor becomes a split tensor under the indicated grouping. -/
theorem regroup_pureTensor (v : ((O ⊕ L) ⊕ L) → D → ℂ) :
    regroupTensor (pureTensor v) = splitTensor (firstTwoFactors v) (lastFactors v) := by
  classical
  funext c
  simp [regroupTensor, blockCoordinates, pureTensor, splitTensor, firstTwoFactors,
    lastFactors, Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow, Prod.map]

/-- The direct witness is nonnegative on every pure tensor, after regrouping.
The projected first block and the filtered right block may both be entangled. -/
theorem pureTensor_projectedSwap_nonneg
    (P : Matrix (O → D) (O → D) ℂ)
    (Q : Matrix ((O → D) × (L → D)) ((O → D) × (L → D)) ℂ)
    (B : Matrix (L → D) (L → D) ℂ)
    (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hB : Bᴴ = B) (hPid : P * P = P)
    (v : ((O ⊕ L) ⊕ L) → D → ℂ) :
    0 ≤ (dotProduct (star (regroupTensor (pureTensor v)))
      (projectedSwapWitness P Q B *ᵥ regroupTensor (pureTensor v))).re := by
  classical
  rw [regroup_pureTensor]
  exact projectedSwapWitness_nonneg P Q B hP hQ hB hPid _ _

/-- The `12 + 1 + 1` site partition is exactly order fourteen. -/
def split14one : ((Fin 12 ⊕ Fin 1) ⊕ Fin 1) ≃ Fin 14 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

/-- The `10 + 2 + 2` site partition is exactly order fourteen. -/
def split14two : ((Fin 10 ⊕ Fin 2) ⊕ Fin 2) ≃ Fin 14 :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

end
end LiebBridge
