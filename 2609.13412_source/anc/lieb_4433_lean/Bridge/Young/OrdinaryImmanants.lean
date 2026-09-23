import Bridge.Young.YoungCharacterCompleteness
import Bridge.PateInterfaces

/-! Ordinary characters and immanants defined internally from the verified
Young representations. Non-partition list inputs are assigned zero solely to
match the established list-indexed certificate and normalization interfaces. -/

noncomputable section
namespace LiebBridge.Young.OrdinaryImmanants
open scoped Classical ComplexOrder
open Certificate WitnessShapes YoungCharacterCompleteness

/-- The actual ordinary S14 character family, with its Young-diagram label. -/
def character : CharacterFamily14 := fun p =>
  if hp : IsPartition14 p then character14 ⟨p,hp⟩ else 0

theorem character_eq (p : Shape) (hp : IsPartition14 p) :
    character p = character14 ⟨p,hp⟩ := by
  simp only [character, dif_pos hp]

theorem character_inverse (p : Shape) (g : Equiv.Perm (Fin 14)) :
    character p g⁻¹ = character p g := by
  unfold character
  split_ifs with hp
  · exact YoungCharacter.realCharacter_inverse (partitionDiagram_card p hp) g
  · rfl

/-- The unnormalized ordinary immanants used in the bridge. -/
def immanant (p : Shape) (A : Matrix14) : ℝ := realImmanant (character p) A

theorem immanant_eq (p : Shape) (hp : IsPartition14 p) (A : Matrix14) :
    immanant p A = realImmanant (character14 ⟨p,hp⟩) A := by
  rw [immanant, character_eq p hp]

/-- Hermiticity suffices for reality; no nonsingularity or real-entry premise
is involved in the immanant definition or this theorem. -/
theorem complexImmanant_real (p : Shape) (A : Matrix14) (hA : A.IsHermitian) :
    star (complexImmanant (fun g => (character p g : ℂ)) A) =
      complexImmanant (fun g => (character p g : ℂ)) A :=
  LiebBridge.complexImmanant_star (character p) (character_inverse p) A hA

theorem immanants14_eq (A : Matrix14) : immanants14 character A = fun p => immanant p A := rfl

end LiebBridge.Young.OrdinaryImmanants
