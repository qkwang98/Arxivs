import Bridge.Young.PrefixRepresentation
import Bridge.Young.PrefixDecomposition
import Bridge.Young.YoungProjectors

/-! Identification of the actual embedded character projector with the
initial-shape selector on the genuine standard-tableau basis. -/

noncomputable section
namespace LiebBridge.Young.PrefixProjector

open scoped BigOperators Classical
open BranchingBasis PrefixRepresentation PrefixDecomposition

variable {eta lam nu : YoungDiagram} {m n : ℕ}

/-- The actual character sum in the ambient Young representation, with the
smaller symmetric group embedded by fixing the complementary labels. -/
def projector (hη : eta.card = m+1) (hν : nu.card = n+1) (hm : m+1 ≤ n+1) :
    Module.End ℂ (StandardTableau nu → ℂ) :=
  ((YoungProjectors.degree eta : ℂ) / Fintype.card (Equiv.Perm (Fin (m+1)))) •
    ∑ g : Equiv.Perm (Fin (m+1)), YoungProjectors.character hη g⁻¹ •
      ScalarExtension.representation ℂ hν (prefixEmbedding hm g)

def initialSelector (eta : YoungDiagram) (m : ℕ) :
    Module.End ℂ (StandardTableau nu → ℂ) :=
  DiagonalIrreducibility.diagonal
    (fun t => if initialDiagram t (m+1) = eta then 1 else 0)

theorem projector_on_glued_basis (h : lam ≤ nu)
    (hη : eta.card = m+1) (hLam : lam.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) (a : StandardTableau lam)
    (s : SkewStandardTableau lam nu) (t : StandardTableau nu) :
    projector hη hν hm (Pi.single (glueTableau h a s).val 1) t =
      if ht : HasPrefix lam t then
        if outerTableau h ⟨t,ht⟩ = s then
          CentralProjectorAction.projector
            (FDRep.of (ScalarExtension.representation ℂ hη))
            (FDRep.of (ScalarExtension.representation ℂ hLam))
            (Pi.single a 1) (innerTableau h ⟨t,ht⟩)
        else 0
      else 0 := by
  simp only [projector, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, representation_basis ℂ h hLam hν]
  split_ifs with hp hs
  · simp only [CentralProjectorAction.projector, CentralProjectorAction.centralSum,
      LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul, YoungProjectors.degree_eq_finrank hη]
    change _ =
      ((((Module.finrank ℂ (StandardTableau eta → ℂ) : ℂ) /
          Fintype.card (Equiv.Perm (Fin (m+1)))) •
        ∑ g : Equiv.Perm (Fin (m+1)), YoungProjectors.character hη g⁻¹ •
          ScalarExtension.representation ℂ hLam g (Pi.single a 1)) :
            StandardTableau lam → ℂ) (innerTableau h ⟨t,hp⟩)
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rfl
  · simp
  · simp

/-- On each genuine prefix block the actual projector either retains or
annihilates every basis vector, according to the prefix diagram. -/
theorem projector_glued_basis (h : lam ≤ nu)
    (hη : eta.card = m+1) (hLam : lam.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) (a : StandardTableau lam) (s : SkewStandardTableau lam nu) :
    projector hη hν hm (Pi.single (glueTableau h a s).val 1) =
      if eta = lam then Pi.single (glueTableau h a s).val 1 else 0 := by
  funext t
  simp only [ite_apply]
  rw [projector_on_glued_basis h hη hLam hν hm,
    YoungProjectors.projector_on_simple hη hLam]
  by_cases he : eta = lam
  · simp only [if_pos he, Module.End.one_apply]
    have hi := representation_basis ℂ h hLam hν 1 a s t
    simpa only [map_one, Module.End.one_apply] using hi.symm
  · simp only [if_neg he, LinearMap.zero_apply, Pi.zero_apply]
    split_ifs <;> rfl

theorem initialSelector_single (eta : YoungDiagram) (m : ℕ) (u : StandardTableau nu) :
    initialSelector eta m (Pi.single u 1) =
      if eta = initialDiagram u (m+1) then Pi.single u 1 else 0 := by
  funext t
  simp only [ite_apply]
  by_cases htu : t = u
  · subst t
    simp [initialSelector, DiagonalIrreducibility.diagonal_apply, eq_comm]
  · simp [initialSelector, DiagonalIrreducibility.diagonal_apply,
      Pi.single_apply, htu, Ne.symm htu, apply_ite]

/-- The central-projector/initial-shape-selector identification on the full
ambient tableau module. Every source tableau is covered by its unique prefix. -/
theorem projector_eq_initialSelector (hη : eta.card = m+1) (hν : nu.card = n+1)
    (hm : m+1 ≤ n+1) : projector hη hν hm = initialSelector (nu := nu) eta m := by
  apply LinearMap.pi_ext
  intro u c
  have hsize : m+1 ≤ nu.card := by omega
  let lam := initialDiagram u (m+1)
  have hl : lam ≤ nu := initialDiagram_le u (m+1)
  have hlc : lam.card = m+1 := initialDiagram_card u (m+1) hsize
  let p : PrefixTableau lam nu := ⟨u, hasPrefix_initialDiagram u (m+1) hsize⟩
  have hg : (glueTableau hl (innerTableau hl p) (outerTableau hl p)).val = u :=
    congrArg Subtype.val (glue_restrictions hl p)
  have hp := projector_glued_basis hl hη hlc hν hm (innerTableau hl p) (outerTableau hl p)
  rw [hg] at hp
  have h1 : projector hη hν hm (Pi.single u 1) = initialSelector eta m (Pi.single u 1) := by
    rw [hp, initialSelector_single]
  have he : (Pi.single u c : StandardTableau nu → ℂ) = c • Pi.single u (1 : ℂ) := by
    funext t
    by_cases ht : t = u <;> simp [Pi.single_apply, ht, eq_comm]
  change projector hη hν hm (Pi.single u c) = initialSelector eta m (Pi.single u c)
  rw [he, map_smul, map_smul, h1]

end LiebBridge.Young.PrefixProjector
