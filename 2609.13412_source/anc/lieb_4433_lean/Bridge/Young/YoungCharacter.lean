import Bridge.Young.ScalarExtension
import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Actual Young characters as traces. Scalar extension proves that the
complex characters are rational, and permutation conjugacy proves inverse
invariance. These are structural character facts, not numerical checks. -/

noncomputable section
namespace LiebBridge.Young.YoungCharacter

open scoped BigOperators

theorem trace_eq_sum_coordinates {K B : Type*} [Field K] [Fintype B] [DecidableEq B]
    (T : Module.End K (B → K)) :
    LinearMap.trace K (B → K) T = ∑ b : B, T (Pi.single b 1) b := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K B),
    LinearMap.toMatrix_eq_toMatrix']
  rfl

theorem trace_extend {B : Type*} [Fintype B] [DecidableEq B]
    (T : Module.End ℚ (B → ℚ)) :
    LinearMap.trace ℂ (B → ℂ) (ScalarExtension.extend ℂ T) =
      (LinearMap.trace ℚ (B → ℚ) T : ℂ) := by
  rw [trace_eq_sum_coordinates, trace_eq_sum_coordinates]
  simp only [ScalarExtension.extend_basis_coefficient, Rat.cast_sum]

variable {d : YoungDiagram} {n : ℕ}

def rationalCharacter (hcard : d.card = n+1) : Equiv.Perm (Fin (n+1)) → ℚ :=
  (FDRep.of (YoungRepresentation.representation hcard)).character

def realCharacter (hcard : d.card = n+1) (g : Equiv.Perm (Fin (n+1))) : ℝ :=
  (rationalCharacter hcard g : ℝ)

theorem complex_character_eq_cast (hcard : d.card = n+1) (g : Equiv.Perm (Fin (n+1))) :
    (FDRep.of (ScalarExtension.representation ℂ hcard)).character g =
      (rationalCharacter hcard g : ℂ) := by
  classical
  exact trace_extend (YoungRepresentation.representation hcard g)

theorem permutation_character_inverse {K : Type} [Field K] {m : ℕ}
    (V : FDRep K (Equiv.Perm (Fin m))) (g : Equiv.Perm (Fin m)) :
    V.character g⁻¹ = V.character g := by
  have h : IsConj g g⁻¹ := Equiv.Perm.isConj_iff_cycleType_eq.mpr
    (Equiv.Perm.cycleType_inv g).symm
  obtain ⟨s,hs⟩ := isConj_iff.mp h
  rw [← hs, FDRep.char_conj]

theorem rationalCharacter_inverse (hcard : d.card = n+1) (g : Equiv.Perm (Fin (n+1))) :
    rationalCharacter hcard g⁻¹ = rationalCharacter hcard g :=
  permutation_character_inverse _ g

theorem realCharacter_inverse (hcard : d.card = n+1) (g : Equiv.Perm (Fin (n+1))) :
    realCharacter hcard g⁻¹ = realCharacter hcard g := by
  simp only [realCharacter, rationalCharacter_inverse]

theorem complex_character_eq_real (hcard : d.card = n+1) (g : Equiv.Perm (Fin (n+1))) :
    (FDRep.of (ScalarExtension.representation ℂ hcard)).character g =
      (realCharacter hcard g : ℂ) := by
  rw [complex_character_eq_cast]
  simp [realCharacter]

theorem complex_character_star_inverse (hcard : d.card = n+1)
    (g : Equiv.Perm (Fin (n+1))) :
    star ((FDRep.of (ScalarExtension.representation ℂ hcard)).character g) =
      (FDRep.of (ScalarExtension.representation ℂ hcard)).character g⁻¹ := by
  rw [complex_character_eq_real, complex_character_eq_real, realCharacter_inverse]
  simp

end LiebBridge.Young.YoungCharacter
