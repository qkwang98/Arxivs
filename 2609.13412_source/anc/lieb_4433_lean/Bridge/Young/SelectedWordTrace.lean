import Bridge.Young.SelectedTrace
import Bridge.Young.SuffixWord

/-! The actual two-prefix-projector/suffix-word trace equals the existing
finite evaluator, with the actual inner-tableau dimension as multiplicity. -/

noncomputable section
namespace LiebBridge.Young.SelectedWordTrace
open scoped BigOperators Classical
open Certificate BranchingBasis PrefixProjector CertificateSkewEquiv SuffixWord

variable {eta nu mu : Shape}
  (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hu : mu.Sorted (· ≥ ·))

local instance : Fintype (SkewStandardTableau
    (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn)) := Fintype.ofFinite _

theorem trace_projectors_word {m n q k r : ℕ}
    (hep : ∀ x ∈ eta, 0 < x) (hup : ∀ x ∈ mu, 0 < x)
    (hc : contains nu eta = true)
    (hη : (YoungDiagram.ofRowLens eta he).card = m+1)
    (hν : (YoungDiagram.ofRowLens nu hn).card = n+1)
    (hμ : (YoungDiagram.ofRowLens mu hu).card = q+1)
    (hm : m+1 ≤ n+1) (hq : q+1 ≤ n+1) (hk : m+1+k = q+1)
    (htail : (YoungDiagram.ofRowLens nu hn).card -
      (YoungDiagram.ofRowLens eta he).card = r+1) (word : List (Fin r)) :
    LinearMap.trace ℂ (StandardTableau (YoungDiagram.ofRowLens nu hn) → ℂ)
      (projector hη hν hm * (projector hμ hν hq *
        ScalarExtension.representation ℂ hν
          (permutationWord (diagram_le_of_contains eta nu he hn hc) hν htail word))) =
      (YoungProjectors.degree (YoungDiagram.ofRowLens eta he) : ℂ) *
        (traceWord eta nu mu k (word.map Fin.val) : ℂ) := by
  let e := certificateBasisEquiv eta nu he hn hc
  let M := TraceSemantics.wordMatrix (tableaux eta nu) (word.map Fin.val)
  have hdiag (a : StandardTableau (YoungDiagram.ofRowLens eta he))
      (s : SkewStandardTableau (YoungDiagram.ofRowLens eta he)
        (YoungDiagram.ofRowLens nu hn)) :
      ScalarExtension.representation ℂ hν
        (permutationWord (diagram_le_of_contains eta nu he hn hc) hν htail word)
        (Pi.single (glueTableau (diagram_le_of_contains eta nu he hn hc) a s).val 1)
        (glueTableau (diagram_le_of_contains eta nu he hn hc) a s).val =
        (M (e.symm s) (e.symm s) : ℂ) := by
    have h := certificate_representation_word_matrix ℂ eta nu he hn hc hν htail word
      a a (e.symm s) (e.symm s)
    change _ = if a = a then (M (e.symm s) (e.symm s) : ℂ) else 0 at h
    simpa only [if_true, e, Equiv.apply_symm_apply] using h
  rw [SelectedTrace.trace_two_projectors he hn hu hep hup hc hη hν hμ hm hq hk
    _ (fun s => (M (e.symm s) (e.symm s) : ℂ)) hdiag]
  congr 1
  have hh := (Equiv.sum_comp e (fun s =>
    if prefixShape eta (encode s) k = mu then (M (e.symm s) (e.symm s) : ℂ) else 0)).symm
  rw [hh]
  rw [TraceSemantics.traceWord_eq_matrixTrace eta nu mu k (word.map Fin.val)
    (CertificateTableaux.tableaux_nodup eta nu)]
  simp only [Matrix.trace, TraceSemantics.prefixSelector, Matrix.diag_apply, Matrix.diagonal_mul, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [e, certificateBasisEquiv_encode, Equiv.symm_apply_apply, beq_iff_eq]
  change (if prefixShape eta t.val k = mu then (M t t : ℂ) else 0) =
    (((if prefixShape eta t.val k = mu then (1 : ℚ) else 0) * M t t : ℚ) : ℂ)
  split_ifs <;> simp

end LiebBridge.Young.SelectedWordTrace
