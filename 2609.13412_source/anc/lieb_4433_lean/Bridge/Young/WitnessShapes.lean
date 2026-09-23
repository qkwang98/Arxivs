import Bridge.Certificate
import Bridge.Young.DiagramCardinality
import Bridge.Young.CertificatePrefixShape

/-! Typed geometric data for the twenty previously verified certificate rows.
All row-specific assertions are logical consequences of `witnessMetadataCheck`;
this module performs no new finite certificate evaluation. -/

namespace LiebBridge.Young.WitnessShapes
open LiebBridge.Certificate

/-- Shape and sign information needed to form the actual prefix operators. -/
structure Metadata (w : Witness) : Prop where
  k_cases : w.k = 1 ∨ w.k = 2
  eta_sum : w.eta.sum = 14 - 2 * w.k
  eta_sorted : w.eta.Sorted (· ≥ ·)
  eta_positive : ∀ a ∈ w.eta, 0 < a
  mu_sum : w.mu.sum = 14 - w.k
  mu_sorted : w.mu.Sorted (· ≥ ·)
  mu_positive : ∀ a ∈ w.mu, 0 < a
  eta_contains_mu : contains w.mu w.eta = true
  sign_cases : w.sign = 1 ∨ w.sign = -1

theorem metadata (w : Witness) (hw : w ∈ rows) : Metadata w := by
  have h := List.all_eq_true.mp witnessMetadataCheck w hw
  have ht : (w.k = 1 ∨ w.k = 2) ∧
      w.eta.sum = 14 - 2 * w.k ∧
      w.eta.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ w.eta, 0 < a) ∧
      w.mu.sum = 14 - w.k ∧
      w.mu.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ w.mu, 0 < a) ∧
      contains w.mu w.eta = true ∧ (w.sign = 1 ∨ w.sign = -1) := by
    simpa [witnessMetadataValid, isPartitionOfCheck, List.all_eq_true, and_assoc] using h
  rcases ht with ⟨hk, hes, heo, hep, hms, hmo, hmp, hc, hsgn⟩
  exact ⟨hk, hes, heo, hep, hms, hmo, hmp, hc, hsgn⟩

theorem k_pos (w : Witness) (hw : w ∈ rows) : 0 < w.k := by
  rcases (metadata w hw).k_cases with h | h <;> omega

theorem k_le_two (w : Witness) (hw : w ∈ rows) : w.k ≤ 2 := by
  rcases (metadata w hw).k_cases with h | h <;> omega

def etaDiagram (w : Witness) (hw : w ∈ rows) : YoungDiagram :=
  YoungDiagram.ofRowLens w.eta (metadata w hw).eta_sorted

def muDiagram (w : Witness) (hw : w ∈ rows) : YoungDiagram :=
  YoungDiagram.ofRowLens w.mu (metadata w hw).mu_sorted

@[simp]
theorem etaDiagram_card (w : Witness) (hw : w ∈ rows) :
    (etaDiagram w hw).card = 14 - 2 * w.k := by
  rw [etaDiagram, YoungDiagram.ofRowLens_card, (metadata w hw).eta_sum]

@[simp]
theorem muDiagram_card (w : Witness) (hw : w ∈ rows) :
    (muDiagram w hw).card = 14 - w.k := by
  rw [muDiagram, YoungDiagram.ofRowLens_card, (metadata w hw).mu_sum]

@[simp]
theorem etaDiagram_rowLens (w : Witness) (hw : w ∈ rows) :
    (etaDiagram w hw).rowLens = w.eta :=
  YoungDiagram.rowLens_ofRowLens_eq_self (metadata w hw).eta_positive

@[simp]
theorem muDiagram_rowLens (w : Witness) (hw : w ∈ rows) :
    (muDiagram w hw).rowLens = w.mu :=
  YoungDiagram.rowLens_ofRowLens_eq_self (metadata w hw).mu_positive

theorem etaDiagram_le_muDiagram (w : Witness) (hw : w ∈ rows) :
    etaDiagram w hw ≤ muDiagram w hw :=
  CertificateSkewEquiv.diagram_le_of_contains w.eta w.mu
    (metadata w hw).eta_sorted (metadata w hw).mu_sorted
    (metadata w hw).eta_contains_mu

theorem etaDiagram_card_add (w : Witness) (hw : w ∈ rows) :
    (etaDiagram w hw).card + 2 * w.k = 14 := by
  rw [etaDiagram_card]
  have := k_le_two w hw
  omega

theorem muDiagram_card_add (w : Witness) (hw : w ∈ rows) :
    (muDiagram w hw).card + w.k = 14 := by
  rw [muDiagram_card]
  have := k_le_two w hw
  omega

theorem etaDiagram_card_add_k (w : Witness) (hw : w ∈ rows) :
    (etaDiagram w hw).card + w.k = (muDiagram w hw).card := by
  rw [etaDiagram_card, muDiagram_card]
  have := k_le_two w hw
  omega

/-- The canonical diagram for any of the enumerated partitions of fourteen. -/
def partitionDiagram (p : Shape) (hp : IsPartition14 p) : YoungDiagram :=
  YoungDiagram.ofRowLens p hp.2.1

@[simp]
theorem partitionDiagram_card (p : Shape) (hp : IsPartition14 p) :
    (partitionDiagram p hp).card = 14 := by
  rw [partitionDiagram, YoungDiagram.ofRowLens_card, hp.1]

@[simp]
theorem partitionDiagram_rowLens (p : Shape) (hp : IsPartition14 p) :
    (partitionDiagram p hp).rowLens = p :=
  YoungDiagram.rowLens_ofRowLens_eq_self hp.2.2

theorem etaDiagram_le_partitionDiagram_iff (w : Witness) (hw : w ∈ rows)
    (p : Shape) (hp : IsPartition14 p) :
    etaDiagram w hw ≤ partitionDiagram p hp ↔ contains p w.eta = true :=
  (CertificatePrefixShape.contains_iff_diagram_le w.eta p
    (metadata w hw).eta_sorted hp.2.1 (metadata w hw).eta_positive).symm

theorem muDiagram_le_partitionDiagram_iff (w : Witness) (hw : w ∈ rows)
    (p : Shape) (hp : IsPartition14 p) :
    muDiagram w hw ≤ partitionDiagram p hp ↔ contains p w.mu = true :=
  (CertificatePrefixShape.contains_iff_diagram_le w.mu p
    (metadata w hw).mu_sorted hp.2.1 (metadata w hw).mu_positive).symm

end LiebBridge.Young.WitnessShapes
