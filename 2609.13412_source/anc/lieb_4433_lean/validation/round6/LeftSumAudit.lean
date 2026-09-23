import Bridge.Young.TensorFiniteLocalization
import Bridge.Young.WitnessCoefficients

/-! Actual tensor witness positivity. The coefficient witness is localized
to the already proved contraction theorem with the genuine character
projectors; no positivity assumption about the witness is made. -/

noncomputable section
namespace LiebBridge.Young.TensorWitnessPositivity

open TensorLocalization TensorFiniteLocalization TensorYoungProjectors
open Bridge.ProjectorConvention WitnessCoefficients RealCoefficientAlgebra
open WitnessShapes Certificate
open scoped BigOperators Matrix Kronecker Classical

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem tensorPermMatrix_one : tensorPermMatrix (D := D) (1 : Equiv.Perm (Fin 14)) = 1 := by
  ext a b
  simp [tensorPermMatrix_apply, Matrix.one_apply]

def tensorEtaP (w : Witness) (hw : w ∈ rows) : Matrix (Fin 14 → D) (Fin 14 → D) ℂ :=
  matrixEvaluation tensorPermMatrix (etaCoeff w hw)

def tensorMuQ (w : Witness) (hw : w ∈ rows) : Matrix (Fin 14 → D) (Fin 14 → D) ℂ :=
  matrixEvaluation tensorPermMatrix (muCoeff w hw)

def tensorRightB (w : Witness) : Matrix (Fin 14 → D) (Fin 14 → D) ℂ :=
  matrixB tensorPermMatrix w

def tensorPairF (w : Witness) : Matrix (Fin 14 → D) (Fin 14 → D) ℂ :=
  tensorPermMatrix (if w.k = 1 then WitnessOperators.swap12 else WitnessOperators.swapPairs)

def tensorWitness (w : Witness) (hw : w ∈ rows) : Matrix (Fin 14 → D) (Fin 14 → D) ℂ :=
  matrixEvaluation tensorPermMatrix (witnessCoeff w hw)

theorem tensorWitness_eq (w : Witness) (hw : w ∈ rows) :
    tensorWitness (D := D) w hw = tensorMuQ w hw * tensorRightB w * tensorEtaP w hw *
      tensorPairF w * tensorRightB w * tensorMuQ w hw :=
  matrixEvaluation_witnessCoeff (tensorPermMatrix (D := D)) tensorPermMatrix_mul
    (by
      ext a b
      simp [tensorPermMatrix_apply, Matrix.one_apply]) w hw

theorem outside_sum_localizes (a b : ℕ) (c : Equiv.Perm (Fin a) → ℂ) :
    transportMatrix (D := D) (splitSites a b)
        (∑ g, c g • tensorPermMatrix (prefixInclusion (by omega : a ≤ a+b+b) g)) =
      outsideLift (L := Fin b → D) (∑ g, c g • tensorPermMatrix g) := by
  simp only [map_sum, map_smul, outside_tensor_localizes]
  ext x y
  simp [outsideLift, Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem left_sum_localizes (a b : ℕ) (c : Equiv.Perm (Fin (a+b)) → ℂ) :
    transportMatrix (D := D) (splitSites a b)
        (∑ g, c g • tensorPermMatrix (prefixInclusion (by omega : a+b ≤ a+b+b) g)) =
      leftLift (L := Fin b → D)
        (regroupLeftMatrix (localMatrix a b (∑ g, c g • tensorPermMatrix g))) := by
  simp only [map_sum, map_smul, left_tensor_localizes]
  ext x y
  simp [leftLift, Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem tensorProjector_eq_sum {d : YoungDiagram} {m : ℕ} (hd : d.card = m+1) :
    tensorProjector (D := D) hd =
      ∑ g : Equiv.Perm (Fin (m+1)),
        (((YoungProjectors.degree d : ℂ) / Fintype.card (Equiv.Perm (Fin (m+1)))) *
          YoungProjectors.character hd g⁻¹) • tensorPermMatrix g := by
  rw [tensorProjector, Bridge.CharacterProjector.characterProjector_eq_inverse_sum]
  · simp only [Finset.smul_sum, mul_smul]
  · exact YoungCharacter.permutation_character_inverse _

def prefixTensor {d : YoungDiagram} {m N : ℕ} (hd : d.card = m+1) (hm : m+1 ≤ N) :
    Matrix (Fin N → D) (Fin N → D) ℂ :=
  ∑ g : Equiv.Perm (Fin (m+1)),
    (((YoungProjectors.degree d : ℂ) / Fintype.card (Equiv.Perm (Fin (m+1)))) *
      YoungProjectors.character hd g⁻¹) • tensorPermMatrix (prefixInclusion hm g)

theorem matrixEvaluation_prefix_eq {d : YoungDiagram} {m : ℕ}
    (hd : d.card = m+1) (hm : m+1 ≤ 14) :
    matrixEvaluation (tensorPermMatrix (D := D)) (prefixCoeff hd hm) = prefixTensor hd hm := by
  rw [matrixEvaluation_prefixCoeff]
  simp only [prefixTensor, Finset.smul_sum, mul_smul]
  rfl

theorem outside_prefixTensor {d : YoungDiagram} {m : ℕ}
    (hd : d.card = m+1) (b : ℕ) :
    transportMatrix (D := D) (splitSites (m+1) b) (prefixTensor hd (by omega)) =
      outsideLift (L := Fin b → D) (tensorProjector hd) := by
  rw [prefixTensor, outside_sum_localizes, tensorProjector_eq_sum]

end LiebBridge.Young.TensorWitnessPositivity

#print axioms LiebBridge.Young.TensorWitnessPositivity.left_sum_localizes
