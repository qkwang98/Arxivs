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

def leftProjector (a b : ℕ) {d : YoungDiagram} {m : ℕ} (hd : d.card = m+1)
    (heq : m+1 = a+b) :
    Matrix ((Fin a → D) × (Fin b → D)) ((Fin a → D) × (Fin b → D)) ℂ := by
  have hcard : d.card = a + b := hd.trans heq
  have P : Matrix (Fin (a+b) → D) (Fin (a+b) → D) ℂ := by
    rw [← hcard, hd]
    exact tensorProjector (D := D) hd
  exact regroupLeftMatrix (localMatrix a b P)

private theorem cast_hermitian {s t : ℕ} (h : s = t)
    (P : Matrix (Fin s → D) (Fin s → D) ℂ) (hP : Pᴴ = P) :
    (cast (congrArg (fun n => Matrix (Fin n → D) (Fin n → D) ℂ) h) P)ᴴ =
      cast (congrArg (fun n => Matrix (Fin n → D) (Fin n → D) ℂ) h) P := by
  subst t
  exact hP

theorem leftProjector_hermitian (a b : ℕ) {d : YoungDiagram} {m : ℕ} (hd : d.card = m+1)
    (heq : m+1 = a+b) : (leftProjector (D := D) a b hd heq)ᴴ = leftProjector a b hd heq := by
  have hcard : d.card = a + b := hd.trans heq
  unfold leftProjector
  change (Matrix.reindex _ _ (Matrix.reindex _ _ _))ᴴ =
    Matrix.reindex _ _ (Matrix.reindex _ _ _)
  rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_reindex]
  congr 2
  exact cast_hermitian hcard _
    (cast_hermitian hd.symm _ (tensorProjector_hermitian (D := D) hd))

theorem left_prefixTensor (a b : ℕ) {d : YoungDiagram} {m : ℕ} (hd : d.card = m+1)
    (heq : m+1 = a+b) :
    transportMatrix (D := D) (splitSites a b)
      (prefixTensor hd (by omega : m+1 ≤ a+b+b)) =
        leftLift (L := Fin b → D) (leftProjector a b hd heq) := by
  have hcard : d.card = a + b := hd.trans heq
  have ht (N : ℕ) (e : N = a+b) (hN : N ≤ a+b+b)
      (c : Equiv.Perm (Fin N) → ℂ) :
      transportMatrix (D := D) (splitSites a b)
        (∑ g, c g • tensorPermMatrix (prefixInclusion hN g)) =
      leftLift (L := Fin b → D) (regroupLeftMatrix (localMatrix a b
        (cast (congrArg (fun n => Matrix (Fin n → D) (Fin n → D) ℂ) e)
          (∑ g, c g • tensorPermMatrix g)))) := by
    subst N
    simpa using left_sum_localizes (D := D) a b c
  rw [prefixTensor, ht (m+1) heq]
  rw [← tensorProjector_eq_sum]
  unfold leftProjector
  change leftLift (regroupLeftMatrix (localMatrix a b
      (cast (congrArg (fun n => Matrix (Fin n → D) (Fin n → D) ℂ) heq)
        (tensorProjector hd)))) =
    leftLift (regroupLeftMatrix (localMatrix a b
      (cast (congrArg (fun n => Matrix (Fin n → D) (Fin n → D) ℂ) hcard)
        (cast (congrArg (fun n => Matrix (Fin n → D) (Fin n → D) ℂ) hd.symm)
          (tensorProjector hd)))))
  simp only [cast_cast]

private theorem concrete_one_nonneg (w : Witness) (hw : w ∈ rows) (hk : w.k = 1)
    (v : Fin 14 → D → ℂ) :
    0 ≤ (tensorInner (pureTensor v) (tensorWitness w hw *ᵥ pureTensor v)).re := by
  have hE : (etaDiagram w hw).card = 11+1 := by simp [hk]
  have hU : (muDiagram w hw).card = 12+1 := by simp [hk]
  have hEta : tensorEtaP (D := D) w hw = prefixTensor hE (by omega : 12 ≤ 14) := by
    unfold tensorEtaP etaCoeff
    cases w with
    | mk k eta mu sign weight coefficients =>
      change k = 1 at hk
      subst k
      exact matrixEvaluation_prefix_eq (D := D) hE _
  have hMu : tensorMuQ (D := D) w hw = prefixTensor hU (by omega : 13 ≤ 14) := by
    unfold tensorMuQ muCoeff
    cases w with
    | mk k eta mu sign weight coefficients =>
      change k = 1 at hk
      subst k
      exact matrixEvaluation_prefix_eq (D := D) hU _
  have hP : transportMatrix (D := D) (splitSites 12 1) (tensorEtaP w hw) =
      outsideLift (L := Fin 1 → D) (tensorProjector hE) := by
    rw [hEta]
    exact outside_prefixTensor hE 1
  have hQ : transportMatrix (D := D) (splitSites 12 1) (tensorMuQ w hw) =
      leftLift (L := Fin 1 → D) (leftProjector 12 1 hU rfl) := by
    rw [hMu]
    exact left_prefixTensor 12 1 hU rfl
  have hF : transportMatrix (D := D) (splitSites 12 1) (tensorPairF w) =
      pairSwapMatrix (O := Fin 12 → D) (L := Fin 1 → D) := by
    rw [tensorPairF, hk, if_pos rfl, ← one_swap, transported_permutation]
    exact swap_localizes
  have hB : transportMatrix (D := D) (splitSites 12 1) (tensorRightB w) =
      rightLift (O := Fin 12 → D) (1 : Matrix (Fin 1 → D) (Fin 1 → D) ℂ) := by
    simp only [tensorRightB, matrixB, hk, if_neg (show ¬ (1:ℕ)=2 by omega),
      map_one, rightLift, Matrix.one_kronecker_one]
    ext x y
    simp [transportMatrix, Matrix.reindexAlgEquiv_apply, Matrix.reindex,
      Matrix.submatrix, Matrix.one_apply]
  have hM : transportMatrix (D := D) (splitSites 12 1) (tensorWitness w hw) =
      projectedSwapWitness (tensorProjector hE) (leftProjector 12 1 hU rfl)
        (1 : Matrix (Fin 1 → D) (Fin 1 → D) ℂ) := by
    simp only [tensorWitness_eq, map_mul, hP, hQ, hF, hB, projectedSwapWitness]
  exact pureTensor_nonneg_of_transport (splitSites 12 1) (tensorWitness w hw)
    (tensorProjector hE) (leftProjector 12 1 hU rfl) 1
    (tensorProjector_hermitian hE) (leftProjector_hermitian 12 1 hU rfl)
    (by simp) (tensorProjector_idempotent hE) hM v

private theorem concrete_two_nonneg (w : Witness) (hw : w ∈ rows) (hk : w.k = 2)
    (v : Fin 14 → D → ℂ) :
    0 ≤ (tensorInner (pureTensor v) (tensorWitness w hw *ᵥ pureTensor v)).re := by
  have hE : (etaDiagram w hw).card = 9+1 := by simp [hk]
  have hU : (muDiagram w hw).card = 11+1 := by simp [hk]
  let B : Matrix (Fin 2 → D) (Fin 2 → D) ℂ :=
    (1/2 : ℂ) • (1 + (w.sign : ℂ) • tensorPermMatrix (Equiv.swap (0 : Fin 2) 1))
  have hEta : tensorEtaP (D := D) w hw = prefixTensor hE (by omega : 10 ≤ 14) := by
    unfold tensorEtaP etaCoeff
    cases w with
    | mk k eta mu sign weight coefficients =>
      change k = 2 at hk
      subst k
      exact matrixEvaluation_prefix_eq (D := D) hE _
  have hMu : tensorMuQ (D := D) w hw = prefixTensor hU (by omega : 12 ≤ 14) := by
    unfold tensorMuQ muCoeff
    cases w with
    | mk k eta mu sign weight coefficients =>
      change k = 2 at hk
      subst k
      exact matrixEvaluation_prefix_eq (D := D) hU _
  have hP : transportMatrix (D := D) (splitSites 10 2) (tensorEtaP w hw) =
      outsideLift (L := Fin 2 → D) (tensorProjector hE) := by
    rw [hEta]
    exact outside_prefixTensor hE 2
  have hQ : transportMatrix (D := D) (splitSites 10 2) (tensorMuQ w hw) =
      leftLift (L := Fin 2 → D) (leftProjector 10 2 hU rfl) := by
    rw [hMu]
    exact left_prefixTensor 10 2 hU rfl
  have hF : transportMatrix (D := D) (splitSites 10 2) (tensorPairF w) =
      pairSwapMatrix (O := Fin 10 → D) (L := Fin 2 → D) := by
    rw [tensorPairF, hk, if_neg (show ¬ (2:ℕ)=1 by omega), ← two_swap,
      transported_permutation]
    exact swap_localizes
  have hB : transportMatrix (D := D) (splitSites 10 2) (tensorRightB w) =
      rightLift (O := Fin 10 → D) B := by
    simp only [tensorRightB, matrixB, hk, if_pos rfl, if_true, map_smul, map_add, map_one]
    rw [← two_right_swap, transported_permutation, right_localizes]
    simp only [B, rightLift, Matrix.kronecker_smul, Matrix.kronecker_add,
      Matrix.one_kronecker_one]
    congr 2
    ext x y
    simp [transportMatrix, Matrix.reindexAlgEquiv_apply, Matrix.reindex,
      Matrix.submatrix, Matrix.one_apply]
  have hBH : Bᴴ = B := by
    simp [B, Matrix.conjTranspose_smul, tensorPermMatrix_star, Equiv.swap_inv]
  have hM : transportMatrix (D := D) (splitSites 10 2) (tensorWitness w hw) =
      projectedSwapWitness (tensorProjector hE) (leftProjector 10 2 hU rfl) B := by
    simp only [tensorWitness_eq, map_mul, hP, hQ, hF, hB, projectedSwapWitness]
  exact pureTensor_nonneg_of_transport (splitSites 10 2) (tensorWitness w hw)
    (tensorProjector hE) (leftProjector 10 2 hU rfl) B
    (tensorProjector_hermitian hE) (leftProjector_hermitian 10 2 hU rfl)
    hBH (tensorProjector_idempotent hE) hM v

/-- The actual coefficient-defined witness is nonnegative on every complex
pure tensor. The two certified site splits localize it to the established
explicit contraction/squared-norm theorem. -/
theorem concrete_witness_nonneg (w : Witness) (hw : w ∈ rows)
    (v : Fin 14 → D → ℂ) :
    0 ≤ (tensorInner (pureTensor v)
      (matrixEvaluation tensorPermMatrix (witnessCoeff w hw) *ᵥ pureTensor v)).re := by
  rcases (metadata w hw).k_cases with hk | hk
  · exact concrete_one_nonneg w hw hk v
  · exact concrete_two_nonneg w hw hk v

end LiebBridge.Young.TensorWitnessPositivity
