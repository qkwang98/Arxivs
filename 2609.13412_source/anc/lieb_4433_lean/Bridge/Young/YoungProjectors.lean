import Bridge.Young.YoungFDRep
import Bridge.Young.YoungCharacter
import Bridge.Young.CentralProjectorAction
import Bridge.CharacterProjector

/-! Instantiate the established character-projector algebra with the actual
Young characters. The degree here is the proven dimension of the tableau
module; no numerical hook quotient is substituted for that dimension. -/

noncomputable section
namespace LiebBridge.Young.YoungProjectors

open scoped BigOperators Classical Matrix ComplexOrder
open CategoryTheory

variable {d eta nu : YoungDiagram} {n : ℕ}

def degree (d : YoungDiagram) : ℕ := Fintype.card (StandardTableau d)

theorem degree_ne_zero (d : YoungDiagram) : degree d ≠ 0 := Fintype.card_ne_zero

theorem degree_eq_finrank (hcard : d.card = n+1) :
    degree d = Module.finrank ℂ (FDRep.of (ScalarExtension.representation ℂ hcard)) :=
  (Module.finrank_fintype_fun_eq_card (R := ℂ) (η := StandardTableau d)).symm

def character (hcard : d.card = n+1) : Equiv.Perm (Fin (n+1)) → ℂ :=
  (FDRep.of (ScalarExtension.representation ℂ hcard)).character

theorem character_star_inverse (hcard : d.card = n+1)
    (g : Equiv.Perm (Fin (n+1))) : star (character hcard g) = character hcard g⁻¹ :=
  YoungCharacter.complex_character_star_inverse hcard g

theorem character_convolution (hcard : d.card = n+1) (k : Equiv.Perm (Fin (n+1))) :
    (∑ g : Equiv.Perm (Fin (n+1)), character hcard g * character hcard (g⁻¹*k)) =
      ((Fintype.card (Equiv.Perm (Fin (n+1))) : ℂ) / degree d) * character hcard k := by
  letI := YoungFDRep.simple ℂ hcard
  simpa only [degree_eq_finrank hcard, character] using
    CentralProjectorAction.character_convolution
      (FDRep.of (ScalarExtension.representation ℂ hcard)) k

/-- The actual Young character projector acts on the actual simple modules
according to equality of their Young diagrams. -/
theorem projector_on_simple (hη : eta.card = n+1) (hν : nu.card = n+1) :
    CentralProjectorAction.projector
      (FDRep.of (ScalarExtension.representation ℂ hη))
      (FDRep.of (ScalarExtension.representation ℂ hν)) =
        if eta = nu then 1 else 0 := by
  classical
  letI := YoungFDRep.simple ℂ hη
  letI := YoungFDRep.simple ℂ hν
  rw [CentralProjectorAction.projector_eq, YoungFDRep.nonempty_iso_iff]

variable {N : Type*} [Fintype N]

/-- Idempotence of the existing matrix projector formula now instantiated with
the constructed ordinary Young character and its actual dimension. -/
theorem matrixProjector_idempotent (hcard : d.card = n+1)
    (U : Equiv.Perm (Fin (n+1)) → Matrix N N ℂ)
    (hU : ∀ g h, U (g*h) = U g * U h) :
    Bridge.CharacterProjector.characterProjector U (character hcard) (degree d) *
      Bridge.CharacterProjector.characterProjector U (character hcard) (degree d) =
      Bridge.CharacterProjector.characterProjector U (character hcard) (degree d) :=
  Bridge.CharacterProjector.characterProjector_idempotent U hU _ _
    (degree_ne_zero d) (character_convolution hcard)

/-- Positivity of the actual Young character projector in every finite
unitary matrix representation. Its character identities are all discharged. -/
theorem matrixProjector_posSemidef (hcard : d.card = n+1)
    (U : Equiv.Perm (Fin (n+1)) → Matrix N N ℂ)
    (hU : ∀ g h, U (g*h) = U g * U h)
    (hUstar : ∀ g, (U g)ᴴ = U g⁻¹) :
    (Bridge.CharacterProjector.characterProjector U (character hcard) (degree d)).PosSemidef :=
  Bridge.CharacterProjector.characterProjector_posSemidef U hU hUstar _ _
    (degree_ne_zero d) (character_star_inverse hcard) (character_convolution hcard)

end LiebBridge.Young.YoungProjectors
