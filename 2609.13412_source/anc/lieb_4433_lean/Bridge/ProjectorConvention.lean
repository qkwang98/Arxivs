import Bridge.CharacterProjector
import Bridge.Immanant
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Agreement of the matrix and tensor character-operator conventions

The immanant-facing tensor operator uses `χ (σ⁻¹)`. The generic matrix
projector uses `χ σ`. This module proves their agreement for inversion-
invariant characters, after the standard coordinate matrix identification.
-/

namespace Bridge.ProjectorConvention

open scoped BigOperators
noncomputable section

variable {I D : Type*} [Fintype I] [Fintype D]
  [DecidableEq I] [DecidableEq D]

def tensorPermMatrix (σ : Equiv.Perm I) : Matrix (I → D) (I → D) ℂ :=
  LinearMap.toMatrix' (LiebBridge.tensorPermLinear (D := D) σ)

theorem characterOperator_matrix_eq_characterProjector
    (χ : Equiv.Perm I → ℂ) (degree : ℕ)
    (hχinv : ∀ σ, χ (σ⁻¹) = χ σ) :
    LinearMap.toMatrix' (LiebBridge.characterOperator (D := D) χ degree) =
      CharacterProjector.characterProjector tensorPermMatrix χ degree := by
  rw [CharacterProjector.characterProjector_eq_inverse_sum _ χ degree hχinv]
  simp [LiebBridge.characterOperator, tensorPermMatrix, map_smul, map_sum]

end

end Bridge.ProjectorConvention
