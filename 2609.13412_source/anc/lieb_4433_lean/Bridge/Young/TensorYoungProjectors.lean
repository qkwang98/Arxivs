import Bridge.Young.YoungProjectors
import Bridge.ProjectorConvention

/-! The actual Young character projectors in the established tensor model.
Both unitarity and the character identities are discharged here. -/

noncomputable section
namespace LiebBridge.Young.TensorYoungProjectors

open Bridge.ProjectorConvention YoungProjectors
open scoped Matrix ComplexOrder

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I] [DecidableEq D]

theorem tensorPermMatrix_apply (g : Equiv.Perm I) (a b : I → D) :
    tensorPermMatrix (D := D) g a b = if a ∘ g = b then 1 else 0 := by
  classical
  simp [tensorPermMatrix, LinearMap.toMatrix'_apply, tensorPermLinear, tensorPerm,
    Pi.single_apply, eq_comm]

theorem tensorPermMatrix_mul (g h : Equiv.Perm I) :
    tensorPermMatrix (D := D) (g*h) = tensorPermMatrix g * tensorPermMatrix h := by
  classical
  change LinearMap.toMatrix' (tensorRepresentation (D := D) (g*h)) = _
  rw [map_mul, LinearMap.toMatrix'_mul]
  rfl

theorem tensorPermMatrix_star (g : Equiv.Perm I) :
    (tensorPermMatrix (D := D) g)ᴴ = tensorPermMatrix g⁻¹ := by
  classical
  ext a b
  have he : (b ∘ g = a) ↔ (a ∘ (g⁻¹ : Equiv.Perm I) = b) := by
    constructor
    · intro h
      funext i
      have hi := congrFun h (g⁻¹ i)
      simpa [Function.comp_apply] using hi.symm
    · intro h
      funext i
      have hi := congrFun h (g i)
      simpa [Function.comp_apply] using hi.symm
  simp only [Matrix.conjTranspose_apply, tensorPermMatrix_apply, apply_ite,
    star_one, star_zero, he]
  split_ifs <;> rfl

variable {d : YoungDiagram} {n : ℕ}

def tensorProjector (hcard : d.card = n+1) :
    Matrix (Fin (n+1) → D) (Fin (n+1) → D) ℂ :=
  Bridge.CharacterProjector.characterProjector tensorPermMatrix (character hcard) (degree d)

theorem tensorProjector_posSemidef (hcard : d.card = n+1) :
    (tensorProjector (D := D) hcard).PosSemidef :=
  matrixProjector_posSemidef hcard tensorPermMatrix tensorPermMatrix_mul tensorPermMatrix_star

theorem tensorProjector_idempotent (hcard : d.card = n+1) :
    tensorProjector (D := D) hcard * tensorProjector hcard = tensorProjector hcard :=
  matrixProjector_idempotent hcard tensorPermMatrix tensorPermMatrix_mul

theorem tensorProjector_hermitian (hcard : d.card = n+1) :
    (tensorProjector (D := D) hcard)ᴴ = tensorProjector hcard :=
  (tensorProjector_posSemidef hcard).isHermitian

end LiebBridge.Young.TensorYoungProjectors
