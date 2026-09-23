import Bridge.Young.TensorYoungProjectors
import Bridge.TensorWitness
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Exact localization of position permutations in the existing finite
tensor-coordinate model. Reindexing preserves products and expectations. -/

noncomputable section
namespace LiebBridge.Young.TensorLocalization

open Bridge.ProjectorConvention TensorYoungProjectors
open scoped BigOperators Matrix Kronecker

variable {O L I D : Type*} [Fintype O] [Fintype L] [Fintype I] [Fintype D]
  [DecidableEq O] [DecidableEq L] [DecidableEq I] [DecidableEq D]

abbrev Sites (O L : Type*) := (O ⊕ L) ⊕ L
abbrev Coordinates (O L D : Type*) := ((O → D) × (L → D)) × (L → D)

def outsidePerm (g : Equiv.Perm O) : Equiv.Perm (Sites O L) :=
  Equiv.sumCongr (Equiv.sumCongr g (Equiv.refl L)) (Equiv.refl L)

def leftPerm (g : Equiv.Perm (O ⊕ L)) : Equiv.Perm (Sites O L) :=
  Equiv.sumCongr g (Equiv.refl L)

def rightPerm (g : Equiv.Perm L) : Equiv.Perm (Sites O L) :=
  Equiv.sumCongr (Equiv.refl (O ⊕ L)) g

def swapBlocks : Equiv.Perm (Sites O L) where
  toFun := fun x => match x with
    | Sum.inl (Sum.inl o) => Sum.inl (Sum.inl o)
    | Sum.inl (Sum.inr l) => Sum.inr l
    | Sum.inr l => Sum.inl (Sum.inr l)
  invFun := fun x => match x with
    | Sum.inl (Sum.inl o) => Sum.inl (Sum.inl o)
    | Sum.inl (Sum.inr l) => Sum.inr l
    | Sum.inr l => Sum.inl (Sum.inr l)
  left_inv := by rintro ((o|l)|l) <;> rfl
  right_inv := by rintro ((o|l)|l) <;> rfl

def regroupMatrix : Matrix (Sites O L → D) (Sites O L → D) ℂ ≃ₐ[ℂ]
    Matrix (Coordinates O L D) (Coordinates O L D) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ blockCoordinates

def firstCoordinates : ((O ⊕ L) → D) ≃ ((O → D) × (L → D)) :=
  Equiv.sumArrowEquivProdArrow O L D

def regroupLeftMatrix : Matrix ((O ⊕ L) → D) ((O ⊕ L) → D) ℂ ≃ₐ[ℂ]
    Matrix ((O → D) × (L → D)) ((O → D) × (L → D)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ firstCoordinates

@[simp] theorem coordinates_symm_outside (c : Coordinates O L D) (o : O) :
    blockCoordinates.symm c (Sum.inl (Sum.inl o)) = c.1.1 o := rfl

@[simp] theorem coordinates_symm_left (c : Coordinates O L D) (l : L) :
    blockCoordinates.symm c (Sum.inl (Sum.inr l)) = c.1.2 l := rfl

@[simp] theorem coordinates_symm_right (c : Coordinates O L D) (l : L) :
    blockCoordinates.symm c (Sum.inr l) = c.2 l := rfl

theorem outside_localizes (g : Equiv.Perm O) :
    regroupMatrix (D := D) (tensorPermMatrix (outsidePerm (L := L) g)) =
      outsideLift (L := L → D) (tensorPermMatrix g) := by
  ext a b
  change tensorPermMatrix (outsidePerm g) (blockCoordinates.symm a) (blockCoordinates.symm b) = _
  rw [tensorPermMatrix_apply]
  have he : (blockCoordinates.symm a ∘ outsidePerm g = blockCoordinates.symm b) ↔
      a.1.1 ∘ g = b.1.1 ∧ a.1.2 = b.1.2 ∧ a.2 = b.2 := by
    constructor
    · intro hh
      exact ⟨funext (fun o => congrFun hh (Sum.inl (Sum.inl o))),
        funext (fun l => congrFun hh (Sum.inl (Sum.inr l))),
        funext (fun l => congrFun hh (Sum.inr l))⟩
    · rintro ⟨ho,hl,hr⟩
      funext x
      rcases x with (o|l)|l
      · exact congrFun ho o
      · exact congrFun hl l
      · exact congrFun hr l
  change (if blockCoordinates.symm a ∘ outsidePerm g = blockCoordinates.symm b then (1 : ℂ) else 0) =
    tensorPermMatrix g a.1.1 b.1.1 * (if a.1.2 = b.1.2 then 1 else 0) *
      (if a.2 = b.2 then 1 else 0)
  rw [tensorPermMatrix_apply]
  simp only [he]
  split_ifs <;> simp_all

theorem left_localizes (g : Equiv.Perm (O ⊕ L)) :
    regroupMatrix (D := D) (tensorPermMatrix (leftPerm g)) =
      leftLift (L := L → D) (regroupLeftMatrix (tensorPermMatrix g)) := by
  ext a b
  change tensorPermMatrix (leftPerm g) (blockCoordinates.symm a) (blockCoordinates.symm b) = _
  rw [tensorPermMatrix_apply]
  have he : (blockCoordinates.symm a ∘ leftPerm g = blockCoordinates.symm b) ↔
      firstCoordinates.symm a.1 ∘ g = firstCoordinates.symm b.1 ∧ a.2 = b.2 := by
    constructor
    · intro hh
      exact ⟨funext (fun x => congrFun hh (Sum.inl x)),
        funext (fun l => congrFun hh (Sum.inr l))⟩
    · rintro ⟨hl,hr⟩
      funext x
      rcases x with x|l
      · exact congrFun hl x
      · exact congrFun hr l
  change (if blockCoordinates.symm a ∘ leftPerm g = blockCoordinates.symm b then (1 : ℂ) else 0) =
    tensorPermMatrix g (firstCoordinates.symm a.1) (firstCoordinates.symm b.1) *
      (1 : Matrix (L → D) (L → D) ℂ) a.2 b.2
  rw [tensorPermMatrix_apply]
  simp only [he, Matrix.one_apply]
  split_ifs <;> simp_all

theorem right_localizes (g : Equiv.Perm L) :
    regroupMatrix (D := D) (tensorPermMatrix (rightPerm (O := O) g)) =
      rightLift (O := O → D) (tensorPermMatrix g) := by
  ext a b
  change tensorPermMatrix (rightPerm g) (blockCoordinates.symm a) (blockCoordinates.symm b) = _
  rw [tensorPermMatrix_apply]
  have he : (blockCoordinates.symm a ∘ rightPerm g = blockCoordinates.symm b) ↔
      a.1 = b.1 ∧ a.2 ∘ g = b.2 := by
    constructor
    · intro hh
      exact ⟨Prod.ext (funext (fun o => congrFun hh (Sum.inl (Sum.inl o))))
        (funext (fun l => congrFun hh (Sum.inl (Sum.inr l)))),
        funext (fun l => congrFun hh (Sum.inr l))⟩
    · rintro ⟨hl,hr⟩
      funext x
      rcases x with (o|l)|l
      · exact congrFun (congrArg Prod.fst hl) o
      · exact congrFun (congrArg Prod.snd hl) l
      · exact congrFun hr l
  change (if blockCoordinates.symm a ∘ rightPerm g = blockCoordinates.symm b then (1 : ℂ) else 0) =
    (if a.1 = b.1 then 1 else 0) * tensorPermMatrix g a.2 b.2
  rw [tensorPermMatrix_apply]
  simp only [he]
  split_ifs <;> simp_all

theorem swap_localizes :
    regroupMatrix (D := D) (tensorPermMatrix (swapBlocks (O := O) (L := L))) =
      pairSwapMatrix (O := O → D) (L := L → D) := by
  ext a b
  change tensorPermMatrix swapBlocks (blockCoordinates.symm a) (blockCoordinates.symm b) = _
  rw [tensorPermMatrix_apply]
  have he : (blockCoordinates.symm a ∘ swapBlocks = blockCoordinates.symm b) ↔
      b = ((a.1.1,a.2),a.1.2) := by
    constructor
    · intro hh
      exact Prod.ext (Prod.ext
        (funext (fun o => (congrFun hh (Sum.inl (Sum.inl o))).symm))
        (funext (fun l => (congrFun hh (Sum.inl (Sum.inr l))).symm)))
        (funext (fun l => (congrFun hh (Sum.inr l)).symm))
    · intro hb
      subst b
      funext x
      rcases x with (o|l)|l <;> rfl
  simp only [he, pairSwapMatrix]
  split_ifs <;> rfl

/-- Pull a configuration back along a position equivalence and group its
three blocks. This fixes the conjugation convention explicitly. -/
def coordinates (ψ : Sites O L ≃ I) : (I → D) ≃ Coordinates O L D :=
  (Equiv.arrowCongr ψ.symm (Equiv.refl D)).trans blockCoordinates

def transportMatrix (ψ : Sites O L ≃ I) :
    Matrix (I → D) (I → D) ℂ ≃ₐ[ℂ] Matrix (Coordinates O L D) (Coordinates O L D) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (coordinates ψ)

def transportVector (ψ : Sites O L ≃ I) (x : Tensor I D) : Coordinates O L D → ℂ :=
  fun c => x ((coordinates ψ).symm c)

theorem transported_permutation (ψ : Sites O L ≃ I) (g : Equiv.Perm (Sites O L)) :
    transportMatrix (D := D) ψ (tensorPermMatrix (ψ.permCongr g)) =
      regroupMatrix (tensorPermMatrix g) := by
  ext a b
  change tensorPermMatrix (ψ.permCongr g) ((coordinates ψ).symm a) ((coordinates ψ).symm b) =
    tensorPermMatrix g (blockCoordinates.symm a) (blockCoordinates.symm b)
  simp only [tensorPermMatrix_apply]
  congr 1
  apply propext
  constructor
  · intro he
    funext j
    have hj := congrFun he (ψ j)
    simpa [coordinates, Function.comp_apply] using hj
  · intro he
    funext i
    have hi := congrFun he (ψ.symm i)
    simpa [coordinates, Function.comp_apply] using hi

theorem transportVector_mulVec (ψ : Sites O L ≃ I)
    (M : Matrix (I → D) (I → D) ℂ) (x : Tensor I D) :
    transportMatrix ψ M *ᵥ transportVector ψ x = transportVector ψ (M *ᵥ x) := by
  have hc : transportVector ψ x ∘ (coordinates ψ) = x := by
    funext c
    simp [transportVector]
  change M.submatrix (coordinates ψ).symm (coordinates ψ).symm *ᵥ transportVector ψ x = _
  rw [Matrix.submatrix_mulVec_equiv]
  change (M *ᵥ (transportVector ψ x ∘ coordinates ψ)) ∘ (coordinates ψ).symm = _
  rw [hc]
  rfl

theorem transportVector_inner (ψ : Sites O L ≃ I) (x y : Tensor I D) :
    dotProduct (star (transportVector ψ x)) (transportVector ψ y) = tensorInner x y := by
  exact Equiv.sum_comp (coordinates ψ).symm (fun c => star (x c) * y c)

theorem transport_pureTensor (ψ : Sites O L ≃ I) (v : I → D → ℂ) :
    transportVector ψ (pureTensor v) = regroupTensor (pureTensor (fun j => v (ψ j))) := by
  funext c
  change (∏ i, v i (((coordinates ψ).symm c) i)) =
    ∏ j, v (ψ j) (blockCoordinates.symm c j)
  simpa [coordinates] using (Equiv.prod_comp ψ (fun i => v i (((coordinates ψ).symm c) i))).symm

theorem transport_expectation (ψ : Sites O L ≃ I)
    (M : Matrix (I → D) (I → D) ℂ) (x : Tensor I D) :
    dotProduct (star (transportVector ψ x)) (transportMatrix ψ M *ᵥ transportVector ψ x) =
      tensorInner x (M *ᵥ x) := by
  rw [transportVector_mulVec, transportVector_inner]

/-- A concrete localized-matrix equality is sufficient to transport the
established contraction inequality to actual pure tensors. -/
theorem pureTensor_nonneg_of_transport (ψ : Sites O L ≃ I)
    (M : Matrix (I → D) (I → D) ℂ)
    (P : Matrix (O → D) (O → D) ℂ)
    (Q : Matrix ((O → D) × (L → D)) ((O → D) × (L → D)) ℂ)
    (B : Matrix (L → D) (L → D) ℂ)
    (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hB : Bᴴ = B) (hPid : P*P=P)
    (hM : transportMatrix ψ M = projectedSwapWitness P Q B) (v : I → D → ℂ) :
    0 ≤ (tensorInner (pureTensor v) (M *ᵥ pureTensor v)).re := by
  rw [← transport_expectation ψ, hM, transport_pureTensor]
  exact pureTensor_projectedSwap_nonneg P Q B hP hQ hB hPid _

end LiebBridge.Young.TensorLocalization
