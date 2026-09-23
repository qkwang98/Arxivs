import Bridge.Young.ScalarExtension
import Bridge.Young.SeminormalEdges
import Bridge.Young.ContentSeparation
import Bridge.Young.TableauExistence

/-! Absolute irreducibility of the actual Young representation. Every
hypothesis of the separating-diagonal argument is discharged on the genuine
standard-tableau basis. In particular the theorem applies over ℂ. -/

noncomputable section
namespace LiebBridge.Young.YoungIrreducibility

open StandardTableau DiagonalIrreducibility

variable (K : Type*) [Field K] [CharZero K]
variable {d : YoungDiagram} {n : ℕ}

local instance : DecidableEq (StandardTableau d) := Classical.decEq _

def contentTuple (hcard : d.card = n+1) (i : Fin (n+1)) (t : StandardTableau d) : K :=
  (t.rationalContent ⟨i.val, by omega⟩ : K)

theorem contentTuple_separates (hcard : d.card = n+1) :
    Separates (contentTuple K hcard) := by
  intro t u htu
  obtain ⟨i,hi⟩ := exists_content_ne htu
  refine ⟨⟨i.val, by omega⟩, ?_⟩
  change (t.rationalContent i : K) ≠ (u.rationalContent i : K)
  exact_mod_cast hi

theorem contentTuple_zero (hcard : d.card = n+1) :
    diagonal (contentTuple K hcard 0) = 0 := by
  have he : diagonal (contentTuple K hcard 0) =
      ScalarExtension.extend K (contentOperator ⟨0, by omega⟩) := by
    rw [ScalarExtension.contentOperator_eq_diagonal, ScalarExtension.extend_diagonal]
    rfl
  rw [he, contentOperator_of_label_zero _ rfl, map_zero]

theorem contentTuple_recurrence (hcard : d.card = n+1) (i : Fin n) :
    diagonal (contentTuple K hcard i.succ) =
      ScalarExtension.representation K hcard (Equiv.swap i.castSucc i.succ) *
        diagonal (contentTuple K hcard i.castSucc) *
        ScalarExtension.representation K hcard (Equiv.swap i.castSucc i.succ) +
        ScalarExtension.representation K hcard (Equiv.swap i.castSucc i.succ) := by
  simp only [ScalarExtension.representation_adjacent]
  have hdiag (k : Fin (n+1)) : diagonal (contentTuple K hcard k) =
      ScalarExtension.extend K (contentOperator ⟨k.val, by omega⟩) := by
    rw [ScalarExtension.contentOperator_eq_diagonal, ScalarExtension.extend_diagonal]
    rfl
  rw [hdiag, hdiag]
  exact ScalarExtension.extended_content_recurrence K
    (YoungRepresentation.leftIndex hcard i) (YoungRepresentation.rightIndex hcard i) rfl

theorem allowedStep_coefficientEdge (hcard : d.card = n+1)
    (t u : StandardTableau d) (htu : AllowedStep t u) :
    CoefficientEdge (fun i : Fin n =>
      ScalarExtension.representation K hcard (Equiv.swap i.castSucc i.succ)) t u := by
  obtain ⟨i,j,hij,hs,rfl⟩ := htu
  let k : Fin n := ⟨i.val, by have hj := j.isLt; omega⟩
  refine ⟨k, ?_⟩
  change ScalarExtension.representation K hcard (Equiv.swap k.castSucc k.succ)
    (Pi.single t 1) (t.adjacentSwap i j hij) ≠ 0
  rw [ScalarExtension.representation_adjacent]
  change ScalarExtension.extend K (YoungRepresentation.adjacentOperator hcard k)
    (Pi.single t 1) (t.adjacentSwap i j hij) ≠ 0
  rw [ScalarExtension.extend_basis_coefficient]
  have hi : YoungRepresentation.leftIndex hcard k = i := Fin.ext rfl
  have hj : YoungRepresentation.rightIndex hcard k = j := Fin.ext (by simpa using hij.symm)
  have he : YoungRepresentation.adjacentOperator hcard k = generator i j hij := by
    unfold YoungRepresentation.adjacentOperator
    simp only [hi,hj]
  rw [he]
  exact_mod_cast generator_allowed_coefficient_ne_zero t i j hij hs

theorem coefficient_connected (hcard : d.card = n+1) (t u : StandardTableau d) :
    Relation.ReflTransGen (CoefficientEdge (fun i : Fin n =>
      ScalarExtension.representation K hcard (Equiv.swap i.castSucc i.succ))) t u :=
  (reachable t u).mono (fun t u h => allowedStep_coefficientEdge K hcard t u h)

/-- The actual Young tableau representation is irreducible over every
characteristic-zero field, and hence absolutely irreducible over ℚ. -/
theorem isSimpleModule (hcard : d.card = n+1) :
    IsSimpleModule (MonoidAlgebra K (Equiv.Perm (Fin (n+1))))
      (ScalarExtension.representation K hcard).asModule := by
  exact representation_isSimpleModule_of_recurrence
    (ScalarExtension.representation K hcard) (contentTuple K hcard)
    (contentTuple_separates K hcard) (fun i => Equiv.swap i.castSucc i.succ)
    (contentTuple_zero K hcard) (contentTuple_recurrence K hcard)
    (coefficient_connected K hcard)

/-- The complex version used by the witness character projectors. -/
theorem complex_isSimpleModule (hcard : d.card = n+1) :
    IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin (n+1))))
      (ScalarExtension.representation ℂ hcard).asModule := isSimpleModule ℂ hcard

end LiebBridge.Young.YoungIrreducibility
