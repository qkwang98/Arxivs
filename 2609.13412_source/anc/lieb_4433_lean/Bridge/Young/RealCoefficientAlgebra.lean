import Bridge.CharacterProjector
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Real finite-group coefficients and their exact evaluation in complex
matrix representations. Convolution preserves the stated operator order. -/

noncomputable section
namespace LiebBridge.Young.RealCoefficientAlgebra
open scoped BigOperators
open Bridge.CharacterProjector

variable {G H N : Type*} [Group G] [Fintype G] [Fintype H] [Fintype N]

def realConvolution (c d : G → ℝ) (g : G) : ℝ :=
  ∑ h : G, c h * d (h⁻¹ * g)

def pushforward (e : H → G) (c : H → ℝ) (g : G) : ℝ := by
  classical
  exact ∑ h : H, if e h = g then c h else 0

def delta (a : G) (g : G) : ℝ := by
  classical
  exact if a = g then 1 else 0

def matrixEvaluation (U : G → Matrix N N ℂ) (c : G → ℝ) : Matrix N N ℂ :=
  weightedOperator U (fun g => (c g : ℂ))

theorem cast_realConvolution (c d : G → ℝ) :
    (fun g => (realConvolution c d g : ℂ)) =
      convolution (fun g => (c g : ℂ)) (fun g => (d g : ℂ)) := by
  funext g
  simp only [realConvolution, convolution, Complex.ofReal_sum, Complex.ofReal_mul]

theorem matrixEvaluation_convolution (U : G → Matrix N N ℂ)
    (hU : ∀ g h, U (g*h) = U g * U h) (c d : G → ℝ) :
    matrixEvaluation U (realConvolution c d) =
      matrixEvaluation U c * matrixEvaluation U d := by
  simp only [matrixEvaluation, cast_realConvolution, weightedOperator_mul U hU]

theorem matrixEvaluation_pushforward (U : G → Matrix N N ℂ)
    (e : H → G) (c : H → ℝ) :
    matrixEvaluation U (pushforward e c) = ∑ h : H, (c h : ℂ) • U (e h) := by
  classical
  simp only [matrixEvaluation, weightedOperator, pushforward, Complex.ofReal_sum,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  simp [ite_smul, eq_comm]

theorem matrixEvaluation_delta (U : G → Matrix N N ℂ) (a : G) :
    matrixEvaluation U (delta a) = U a := by
  classical
  simp [matrixEvaluation, weightedOperator, delta, ite_smul, eq_comm]

theorem matrixEvaluation_add (U : G → Matrix N N ℂ) (c d : G → ℝ) :
    matrixEvaluation U (c+d) = matrixEvaluation U c + matrixEvaluation U d := by
  simp [matrixEvaluation, weightedOperator, add_smul, Finset.sum_add_distrib]

theorem matrixEvaluation_smul (U : G → Matrix N N ℂ) (a : ℝ) (c : G → ℝ) :
    matrixEvaluation U (a • c) = (a : ℂ) • matrixEvaluation U c := by
  simp [matrixEvaluation, weightedOperator, Finset.smul_sum, mul_smul]

theorem matrixEvaluation_trace (U : G → Matrix N N ℂ) (c : G → ℝ) :
    Matrix.trace (matrixEvaluation U c) = ∑ g : G, (c g : ℂ) * Matrix.trace (U g) :=
  weightedOperator_trace U _

section Endomorphism
variable [DecidableEq N]

def endEvaluation (U : G → Module.End ℂ (N → ℂ)) (c : G → ℝ) :
    Module.End ℂ (N → ℂ) := ∑ g : G, (c g : ℂ) • U g

theorem toMatrix_endEvaluation (U : G → Module.End ℂ (N → ℂ)) (c : G → ℝ) :
    LinearMap.toMatrix' (endEvaluation U c) =
      matrixEvaluation (fun g => LinearMap.toMatrix' (U g)) c := by
  simp only [endEvaluation, map_sum, map_smul, matrixEvaluation, weightedOperator]

theorem endEvaluation_convolution (U : G → Module.End ℂ (N → ℂ))
    (hU : ∀ g h, U (g*h) = U g * U h) (c d : G → ℝ) :
    endEvaluation U (realConvolution c d) = endEvaluation U c * endEvaluation U d := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_mul]
  simp only [toMatrix_endEvaluation]
  apply matrixEvaluation_convolution
  intro g h
  rw [hU, LinearMap.toMatrix'_mul]

theorem endEvaluation_pushforward (U : G → Module.End ℂ (N → ℂ))
    (e : H → G) (c : H → ℝ) :
    endEvaluation U (pushforward e c) = ∑ h : H, (c h : ℂ) • U (e h) := by
  apply LinearMap.toMatrix'.injective
  simp only [toMatrix_endEvaluation, matrixEvaluation_pushforward, map_sum, map_smul]

theorem endEvaluation_delta (U : G → Module.End ℂ (N → ℂ)) (a : G) :
    endEvaluation U (delta a) = U a := by
  apply LinearMap.toMatrix'.injective
  rw [toMatrix_endEvaluation, matrixEvaluation_delta]

theorem endEvaluation_add (U : G → Module.End ℂ (N → ℂ)) (c d : G → ℝ) :
    endEvaluation U (c+d) = endEvaluation U c + endEvaluation U d := by
  simp only [endEvaluation, Pi.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

theorem endEvaluation_smul (U : G → Module.End ℂ (N → ℂ)) (a : ℝ) (c : G → ℝ) :
    endEvaluation U (a • c) = (a : ℂ) • endEvaluation U c := by
  simp only [endEvaluation, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.smul_sum, mul_smul]

end Endomorphism
end LiebBridge.Young.RealCoefficientAlgebra
