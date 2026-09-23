import Bridge.Immanant
import Bridge.Normalization

/-!
The four historical dependencies, stated for complex Hermitian PSD matrices.

The ordinary character family has not yet been constructed in this project.
It is therefore a visible parameter. The final arithmetic transfer also has
the bridge as a visible hypothesis: it is NOT the requested completed theorem
conditional only on four historical Pate results.
-/

open scoped ComplexOrder

namespace LiebBridge
noncomputable section

abbrev Matrix14 := Matrix (Fin 14) (Fin 14) ℂ
abbrev CharacterFamily14 := List ℕ → Equiv.Perm (Fin 14) → ℝ

def immanants14 (χ : CharacterFamily14) (A : Matrix14) : List ℕ → ℝ :=
  fun shape => realImmanant (χ shape) A

/-- External historical interface for the ordinary character indexed by `(6,5,3)`. -/
def Pate653 (χ : CharacterFamily14) : Prop :=
  ∀ A : Matrix14, A.PosSemidef → immanants14 χ A [6, 5, 3] / 15015 ≤ permanent A

/-- External historical interface for the ordinary character indexed by `(6,4,4)`. -/
def Pate644 (χ : CharacterFamily14) : Prop :=
  ∀ A : Matrix14, A.PosSemidef → immanants14 χ A [6, 4, 4] / 9009 ≤ permanent A

/-- External historical interface for the ordinary character indexed by `(5,5,4)`. -/
def Pate554 (χ : CharacterFamily14) : Prop :=
  ∀ A : Matrix14, A.PosSemidef → immanants14 χ A [5, 5, 4] / 6006 ≤ permanent A

/-- External historical interface for the ordinary character indexed by `(5,3,3,3)`. -/
def Pate5333 (χ : CharacterFamily14) : Prop :=
  ∀ A : Matrix14, A.PosSemidef → immanants14 χ A [5, 3, 3, 3] / 15015 ≤ permanent A

/-- The desired matrix bridge as a proposition. There is no proof of this
proposition for the ordinary character family in the present project. -/
def Bridge4433 (χ : CharacterFamily14) : Prop :=
  ∀ A : Matrix14, A.PosSemidef →
    Bridge.Normalization.bridgeInequality (immanants14 χ A)

/-- The normalization step for an explicitly supplied bridge. -/
theorem normalizedBridge_of_matrixBridge (χ : CharacterFamily14)
    (hbridge : Bridge4433 χ) (A : Matrix14) (hA : A.PosSemidef) :
    Bridge.Normalization.normalizedBridgeInequality (immanants14 χ A) :=
  Bridge.Normalization.normalizedBridge_of_bridge (hbridge A hA)

/-- Conditional arithmetic transfer, with the missing bridge hypothesis
displayed explicitly. No historical theorem is declared as a Lean axiom. -/
theorem pdc4433_of_bridge_and_four_pate (χ : CharacterFamily14)
    (hbridge : Bridge4433 χ)
    (pate653 : Pate653 χ) (pate644 : Pate644 χ)
    (pate554 : Pate554 χ) (pate5333 : Pate5333 χ)
    (A : Matrix14) (hA : A.PosSemidef) :
    immanants14 χ A [4, 4, 3, 3] / 12012 ≤ permanent A := by
  exact Bridge.Normalization.pdc4433_of_bridge (hbridge A hA)
    (pate653 A hA) (pate644 A hA) (pate554 A hA) (pate5333 A hA)

end
end LiebBridge
