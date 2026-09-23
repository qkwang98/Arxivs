import Bridge.Young.PrefixTrace
import Bridge.Young.CertificatePrefixShape

/-! The two actual character projectors reduce a trace to the intermediate
shape selector. The tail operator is arbitrary here; its word realization is
proved separately in `SuffixWord`. -/

noncomputable section
namespace LiebBridge.Young.SelectedTrace

open scoped BigOperators Classical
open BranchingBasis PrefixDecomposition PrefixProjector CertificateSkewEquiv

variable {eta nu mu : Certificate.Shape}
  (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hu : mu.Sorted (· ≥ ·))

local instance : Fintype (SkewStandardTableau
    (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn)) := Fintype.ofFinite _

/-- Exact trace reduction for the two embedded central projectors. The only
operator input is the diagonal of the explicitly supplied tail operator. -/
theorem trace_two_projectors {m n q k : ℕ}
    (hep : ∀ x ∈ eta, 0 < x) (hup : ∀ x ∈ mu, 0 < x)
    (hc : Certificate.contains nu eta = true)
    (hη : (YoungDiagram.ofRowLens eta he).card = m+1)
    (hν : (YoungDiagram.ofRowLens nu hn).card = n+1)
    (hμ : (YoungDiagram.ofRowLens mu hu).card = q+1)
    (hm : m+1 ≤ n+1) (hq : q+1 ≤ n+1) (hk : m+1+k = q+1)
    (T : Module.End ℂ (StandardTableau (YoungDiagram.ofRowLens nu hn) → ℂ))
    (f : SkewStandardTableau (YoungDiagram.ofRowLens eta he)
      (YoungDiagram.ofRowLens nu hn) → ℂ)
    (hdiag : ∀ a s, T (Pi.single
      (glueTableau (diagram_le_of_contains eta nu he hn hc) a s).val 1)
      (glueTableau (diagram_le_of_contains eta nu he hn hc) a s).val = f s) :
    LinearMap.trace ℂ (StandardTableau (YoungDiagram.ofRowLens nu hn) → ℂ)
      (projector hη hν hm * (projector hμ hν hq * T)) =
      (YoungProjectors.degree (YoungDiagram.ofRowLens eta he) : ℂ) *
        ∑ s, if Certificate.prefixShape eta (encode s) k = mu then f s else 0 := by
  apply PrefixTrace.trace_projector_mul_factor
    (diagram_le_of_contains eta nu he hn hc) hη hν hm
  intro a s
  rw [projector_eq_initialSelector]
  simp only [Module.End.mul_apply, initialSelector, DiagonalIrreducibility.diagonal_apply]
  rw [hdiag]
  have hs := CertificatePrefixShape.prefixShape_eq_iff_initialDiagram
    eta nu mu he hn hu hep hup hc a s k
  rw [hη, hk] at hs
  rw [← hs]
  split_ifs <;> simp

end LiebBridge.Young.SelectedTrace
