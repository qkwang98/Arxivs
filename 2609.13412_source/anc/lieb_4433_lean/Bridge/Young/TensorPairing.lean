import Bridge.Young.RealCoefficientAlgebra
import Bridge.Young.OrdinaryImmanants
import Bridge.Young.TensorYoungProjectors

/-! The real coefficient pairing is exactly the expectation in the established
tensor model. Character pairing is exactly the ordinary Gram immanant, with
the inverse convention proved by reindexing the actual symmetric group. -/

noncomputable section
namespace LiebBridge.Young.TensorPairing
open scoped BigOperators Matrix Classical
open RealCoefficientAlgebra Bridge.ProjectorConvention Bridge.CentralAveraging

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I] [DecidableEq D]

def moment (v : I → D → ℂ) (g : Equiv.Perm I) : ℝ :=
  (tensorInner (pureTensor v) (tensorPerm g (pureTensor v))).re

theorem tensorPermMatrix_mulVec (g : Equiv.Perm I) (x : Tensor I D) :
    tensorPermMatrix g *ᵥ x = tensorPerm g x := by
  funext a
  simp [Matrix.mulVec, dotProduct, TensorYoungProjectors.tensorPermMatrix_apply,
    ite_mul, tensorPerm]

theorem evaluation_pairing (c : Equiv.Perm I → ℝ) (v : I → D → ℂ) :
    (tensorInner (pureTensor v)
      (matrixEvaluation tensorPermMatrix c *ᵥ pureTensor v)).re = pairing c (moment v) := by
  have hv : matrixEvaluation tensorPermMatrix c *ᵥ pureTensor v =
      ∑ g : Equiv.Perm I, (c g : ℂ) • tensorPerm g (pureTensor v) := by
    funext a
    simp only [matrixEvaluation, Bridge.CharacterProjector.weightedOperator,
      Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    rw [← Finset.mul_sum]
    congr 1
    exact congrFun (tensorPermMatrix_mulVec g (pureTensor v)) a
  rw [hv]
  simp only [tensorInner_sum_right, tensorInner_smul_right, Complex.re_sum,
    Complex.re_ofReal_mul, pairing, moment]

theorem moment_conjugate (v : I → D → ℂ) (a g : Equiv.Perm I) :
    moment v (a*g*a⁻¹) = moment (fun i => v (a i)) g := by
  unfold moment
  congr 1
  have h := tensorInner_perm a⁻¹ (pureTensor v)
    (tensorPerm (a*g*a⁻¹) (pureTensor v))
  have hg : a⁻¹*(a*g*a⁻¹) = g*a⁻¹ := by group
  rw [← tensorPerm_mul, hg, tensorPerm_mul] at h
  rw [tensorPerm_pureTensor] at h
  simpa only [inv_inv] using h.symm

theorem character_pairing (χ : Equiv.Perm I → ℝ)
    (hχ : ∀ g, χ g⁻¹=χ g) (v : I → D → ℂ) :
    pairing χ (moment v) = realImmanant χ (gramMatrix v) := by
  simp only [pairing, moment, tensorInner_perm_pureTensor, realImmanant,
    complexImmanant, Complex.re_sum, Complex.re_ofReal_mul]
  have h := Equiv.sum_comp (Equiv.inv (Equiv.Perm I))
    (fun g => χ g * (∏ i, gramMatrix v i (g i)).re)
  simpa only [Equiv.inv_apply, hχ] using h

/-- Conjugated test functions are expectations on another pure tensor. -/
theorem conjugated_pairing_nonneg (c : Equiv.Perm I → ℝ)
    (h : ∀ v : I → D → ℂ, 0 ≤ (tensorInner (pureTensor v)
      (matrixEvaluation tensorPermMatrix c *ᵥ pureTensor v)).re)
    (v : I → D → ℂ) (a : Equiv.Perm I) :
    0 ≤ pairing c (fun g => moment v (a*g*a⁻¹)) := by
  simp only [moment_conjugate]
  rw [← evaluation_pairing]
  exact h _

end LiebBridge.Young.TensorPairing
