import Bridge.Young.TensorLocalization
import Bridge.Young.PrefixRepresentation
import Bridge.Young.WitnessOperators

/-! The canonical finite-position splits and the actual prefix embeddings.
All equalities are extensional on positions; no permutation group is enumerated. -/

noncomputable section
namespace LiebBridge.Young.TensorFiniteLocalization

open TensorLocalization Bridge.ProjectorConvention TensorYoungProjectors
open scoped BigOperators Matrix Kronecker Classical

def splitSites (a b : ℕ) : Sites (Fin a) (Fin b) ≃ Fin (a+b+b) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def prefixInclusion {a N : ℕ} (h : a ≤ N) : Equiv.Perm (Fin a) →* Equiv.Perm (Fin N) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h)

theorem prefixInclusion_apply {a N : ℕ} (h : a ≤ N) (g : Equiv.Perm (Fin a)) (i : Fin a) :
    prefixInclusion h g (Fin.castLE h i) = Fin.castLE h (g i) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem prefixInclusion_fixed {a N : ℕ} (h : a ≤ N) (g : Equiv.Perm (Fin a))
    (i : Fin N) (hi : a ≤ i.val) : prefixInclusion h g i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_not_mem
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  have := j.isLt
  change j.val = i.val at hh
  omega

theorem outside_prefix (a b : ℕ) (g : Equiv.Perm (Fin a)) :
    (splitSites a b).permCongr (outsidePerm (L := Fin b) g) =
      prefixInclusion (by omega : a ≤ a+b+b) g := by
  apply Equiv.ext
  intro i
  obtain ⟨x,rfl⟩ := (splitSites a b).surjective i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases x with (o|l)|l
  · change Fin.castLE (by omega : a ≤ a+b+b) (g o) =
      prefixInclusion _ g (Fin.castLE (by omega : a ≤ a+b+b) o)
    exact (prefixInclusion_apply _ g o).symm
  · rw [prefixInclusion_fixed _ g _ (by change a ≤ a+l.val; omega)]
    rfl
  · rw [prefixInclusion_fixed _ g _ (by change a ≤ a+b+l.val; omega)]
    rfl

theorem left_prefix (a b : ℕ) (g : Equiv.Perm (Fin (a+b))) :
    (splitSites a b).permCongr
        (leftPerm ((finSumFinEquiv : (Fin a ⊕ Fin b) ≃ Fin (a+b)).symm.permCongr g)) =
      prefixInclusion (by omega : a+b ≤ a+b+b) g := by
  apply Equiv.ext
  intro i
  obtain ⟨x,rfl⟩ := (splitSites a b).surjective i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rcases x with x|l
  · have he (j : Fin (a+b)) :
        splitSites a b (Sum.inl ((finSumFinEquiv : (Fin a ⊕ Fin b) ≃ Fin (a+b)).symm j)) =
          Fin.castLE (by omega : a+b ≤ a+b+b) j := by
      simp [splitSites]
      rfl
    change splitSites a b (Sum.inl ((finSumFinEquiv : (Fin a ⊕ Fin b) ≃ Fin (a+b)).symm
      (g (finSumFinEquiv x)))) = _
    rw [he]
    have hx : splitSites a b (Sum.inl x) =
        Fin.castLE (by omega : a+b ≤ a+b+b) (finSumFinEquiv x) := rfl
    rw [hx, prefixInclusion_apply]
  · rw [prefixInclusion_fixed _ g _ (by change a+b ≤ a+b+l.val; omega)]
    rfl

def localCoordinates (a b : ℕ) {D : Type*} :
    (Fin (a+b) → D) ≃ ((Fin a ⊕ Fin b) → D) :=
  Equiv.arrowCongr (finSumFinEquiv : (Fin a ⊕ Fin b) ≃ Fin (a+b)).symm (Equiv.refl D)

def localMatrix (a b : ℕ) {D : Type*} [Fintype D] [DecidableEq D] :
    Matrix (Fin (a+b) → D) (Fin (a+b) → D) ℂ ≃ₐ[ℂ]
      Matrix ((Fin a ⊕ Fin b) → D) ((Fin a ⊕ Fin b) → D) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (localCoordinates a b)

theorem local_permutation (a b : ℕ) {D : Type*} [Fintype D] [DecidableEq D]
    (g : Equiv.Perm (Fin (a+b))) :
    localMatrix a b (tensorPermMatrix (D := D) g) =
      tensorPermMatrix ((finSumFinEquiv : (Fin a ⊕ Fin b) ≃ Fin (a+b)).symm.permCongr g) := by
  ext c d
  change tensorPermMatrix g ((localCoordinates a b).symm c) ((localCoordinates a b).symm d) = _
  rw [tensorPermMatrix_apply, tensorPermMatrix_apply]
  congr 1
  apply propext
  constructor
  · intro he
    funext x
    have hh := congrFun he (finSumFinEquiv x)
    simpa [localCoordinates] using hh
  · intro he
    funext x
    have hh := congrFun he ((finSumFinEquiv : (Fin a ⊕ Fin b) ≃ Fin (a+b)).symm x)
    simpa [localCoordinates] using hh

theorem outside_tensor_localizes (a b : ℕ) {D : Type*} [Fintype D] [DecidableEq D]
    (g : Equiv.Perm (Fin a)) :
    transportMatrix (D := D) (splitSites a b) (tensorPermMatrix (prefixInclusion (by omega) g)) =
      outsideLift (L := Fin b → D) (tensorPermMatrix g) := by
  rw [← outside_prefix a b g, transported_permutation, outside_localizes]

theorem left_tensor_localizes (a b : ℕ) {D : Type*} [Fintype D] [DecidableEq D]
    (g : Equiv.Perm (Fin (a+b))) :
    transportMatrix (D := D) (splitSites a b) (tensorPermMatrix (prefixInclusion (by omega) g)) =
      leftLift (L := Fin b → D) (regroupLeftMatrix (localMatrix a b (tensorPermMatrix g))) := by
  rw [← left_prefix a b g, transported_permutation, left_localizes, local_permutation]

theorem one_swap : (splitSites 12 1).permCongr (swapBlocks (O := Fin 12) (L := Fin 1)) =
    WitnessOperators.swap12 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

theorem two_swap : (splitSites 10 2).permCongr (swapBlocks (O := Fin 10) (L := Fin 2)) =
    WitnessOperators.swapPairs := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

theorem two_right_swap : (splitSites 10 2).permCongr
    (rightPerm (O := Fin 10) (Equiv.swap (0 : Fin 2) 1)) = WitnessOperators.swap12 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

end LiebBridge.Young.TensorFiniteLocalization
