import Bridge.Young.CertificateSkewEquiv
import Bridge.Young.PrefixDecomposition

/-! The certificate's row-count prefix selector agrees with the actual
intermediate straight Young diagram obtained by gluing a prefix tableau. -/

noncomputable section
namespace LiebBridge.Young.CertificatePrefixShape
open LiebBridge.Certificate CertificateTableaux CertificateSkewEquiv
open BranchingBasis PrefixDecomposition StandardTableau
attribute [local instance] Classical.propDecidable
local instance : BEq Box := instBEqOfDecidableEq

variable {eta nu : YoungDiagram}

theorem mem_take_encode (T : SkewStandardTableau eta nu) (b : SkewCell eta nu) (k : ℕ) :
    b.val.val ∈ (encode T).take k ↔ (T.number b).val < k := by
  rw [mem_take_iff_idxOf_lt (encode T) (encode_nodup T) _
    ((encode_support T _).mpr ⟨b.val.property, b.property⟩), encode_idxOf]

theorem initialDiagram_glue_cells (h : eta ≤ nu) (a : StandardTableau eta)
    (T : SkewStandardTableau eta nu) (k : ℕ) :
    (initialDiagram (glueTableau h a T).val (eta.card + k)).cells =
      eta.cells ∪ ((encode T).take k).toFinset := by
  ext b
  by_cases hnu : b ∈ nu.cells
  · change b ∈ initialCells (glueTableau h a T).val (eta.card + k) ↔ _
    rw [mem_initialCells _ _ ⟨b, hnu⟩, Finset.mem_union, List.mem_toFinset]
    change (glueNumber h a T ⟨b, hnu⟩).val < eta.card + k ↔ _
    by_cases he : b ∈ eta.cells
    · rw [glueNumber_inner h a T ⟨b, hnu⟩ he]
      have hi := (a.number ⟨b, he⟩).isLt
      simp only [he, true_or, iff_true]
      omega
    · rw [glueNumber_outer h a T ⟨b, hnu⟩ he]
      change eta.card + (T.number ⟨⟨b, hnu⟩, he⟩).val < eta.card + k ↔
        b ∈ eta.cells ∨ (⟨⟨b, hnu⟩, he⟩ : SkewCell eta nu).val.val ∈ (encode T).take k
      rw [mem_take_encode]
      simp [he]
  · have hleft : b ∉ (initialDiagram (glueTableau h a T).val (eta.card + k)).cells :=
      fun hb => hnu (initialCells_subset _ _ hb)
    have he : b ∉ eta.cells := fun hb => hnu (h hb)
    have ht : b ∉ (encode T).take k := by
      intro hb
      have hb' : b ∈ encode T := List.mem_of_mem_take hb
      exact hnu ((encode_support T b).mp hb').1
    simp [hleft, he, ht]

theorem rowLen_zero_of_height_le (d : YoungDiagram) (i : ℕ) (hi : d.colLen 0 ≤ i) :
    d.rowLen i = 0 := by
  by_contra hh
  have hp : 0 < d.rowLen i := by omega
  have hm : (i, 0) ∈ d := YoungDiagram.mem_iff_lt_rowLen.mpr hp
  have hk : i < d.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hm
  omega

theorem getD_rowLens (d : YoungDiagram) (i : ℕ) : d.rowLens.getD i 0 = d.rowLen i := by
  by_cases hi : i < d.rowLens.length
  · rw [List.getD_eq_getElem d.rowLens 0 hi, YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default d.rowLens 0 (n := i) (by omega)]
    exact (rowLen_zero_of_height_le d i (by simpa using Nat.le_of_not_gt hi)).symm

theorem rowLen_union_list (d eta : YoungDiagram) (u : Tableau) (hn : u.Nodup)
    (ho : ∀ b ∈ u, b ∉ eta.cells) (hd : d.cells = eta.cells ∪ u.toFinset) (r : ℕ) :
    d.rowLen r = eta.rowLen r + (u.filter (fun b => b.1 == r)).length := by
  have hr : d.row r = eta.row r ∪ (u.toFinset.filter fun b => b.1 = r) := by
    simp only [YoungDiagram.row, hd, Finset.filter_union]
  have hdis : Disjoint (eta.row r) (u.toFinset.filter fun b => b.1 = r) := by
    apply Finset.disjoint_left.mpr
    intro b he hu
    exact ho b (List.mem_toFinset.mp (Finset.mem_filter.mp hu).1)
      (YoungDiagram.mem_row_iff.mp he).1
  rw [YoungDiagram.rowLen_eq_card, hr, Finset.card_union_of_disjoint hdis,
    ← YoungDiagram.rowLen_eq_card]
  congr 1
  have hf : (u.filter (fun b => b.1 == r)).toFinset = u.toFinset.filter (fun b => b.1 = r) := by
    ext b
    simp
  rw [← hf, List.toFinset_card_of_nodup (hn.filter _)]

theorem height_union_list (d eta : YoungDiagram) (u : Tableau) (hn : u.Nodup)
    (hd : d.cells = eta.cells ∪ u.toFinset) : d.colLen 0 ≤ eta.colLen 0 + u.length := by
  have hsub : eta.col 0 ⊆ d.col 0 := by
    intro b hb
    simp only [YoungDiagram.col, Finset.mem_filter] at hb ⊢
    exact ⟨by rw [hd]; exact Finset.mem_union_left _ hb.1, hb.2⟩
  have hdiff : d.col 0 \ eta.col 0 ⊆ u.toFinset := by
    intro b hb
    obtain ⟨hbd, hbe⟩ := Finset.mem_sdiff.mp hb
    have hbd' := YoungDiagram.mem_col_iff.mp hbd
    have hbn : b ∉ eta.cells := by
      intro he
      exact hbe (YoungDiagram.mem_col_iff.mpr ⟨he, hbd'.2⟩)
    have hh : b ∈ eta.cells ∪ u.toFinset := hd ▸ hbd'.1
    exact (Finset.mem_union.mp hh).resolve_left hbn
  have hc := Finset.card_le_card hdiff
  rw [Finset.card_sdiff hsub, List.toFinset_card_of_nodup hn,
    ← YoungDiagram.colLen_eq_card, ← YoungDiagram.colLen_eq_card] at hc
  omega

theorem rowLens_from_bound (d : YoungDiagram) (B : ℕ) (hB : d.colLen 0 ≤ B) :
    ((List.range B).map d.rowLen).filter (fun n => n != 0) = d.rowLens := by
  have hb : B = d.colLen 0 + (B - d.colLen 0) := by omega
  rw [hb, List.range_add, List.map_append, List.filter_append]
  have hp : (((List.range (d.colLen 0)).map d.rowLen).filter (fun n => n != 0)) =
      (List.range (d.colLen 0)).map d.rowLen := by
    apply List.filter_eq_self.mpr
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have hm : (i, 0) ∈ d := YoungDiagram.mem_iff_lt_colLen.mpr (List.mem_range.mp hi)
    have hp : 0 < d.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hm
    simp [Nat.ne_of_gt hp]
  have hz : ((((List.range (B - d.colLen 0)).map (d.colLen 0 + ·)).map d.rowLen).filter
      (fun n => n != 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    simp [rowLen_zero_of_height_le d (d.colLen 0 + i) (by omega)]
  rw [hp, hz, List.append_nil]
  rfl

/-- The executable prefix shape is the canonical row-length list of the
actual intermediate straight tableau, for every choice of the inner tableau. -/
theorem prefixShape_eq_initialDiagram_rowLens (h : eta ≤ nu) (a : StandardTableau eta)
    (T : SkewStandardTableau eta nu) (k : ℕ) :
    Certificate.prefixShape eta.rowLens (encode T) k =
      (initialDiagram (glueTableau h a T).val (eta.card + k)).rowLens := by
  let d := initialDiagram (glueTableau h a T).val (eta.card + k)
  let u := (encode T).take k
  have hu : u.Nodup := (encode_nodup T).take
  have ho : ∀ b ∈ u, b ∉ eta.cells := by
    intro b hb
    exact ((encode_support T b).mp (List.mem_of_mem_take hb)).2
  have hd : d.cells = eta.cells ∪ u.toFinset := initialDiagram_glue_cells h a T k
  have hheight := height_union_list d eta u hu hd
  have hlen : u.length ≤ (encode T).length := by simp [u]
  have hbound : d.colLen 0 ≤ eta.rowLens.length + (encode T).length := by
    rw [YoungDiagram.length_rowLens]
    omega
  have hrow (i : ℕ) : eta.rowLen i + (u.filter (fun b => b.1 == i)).length = d.rowLen i :=
    (rowLen_union_list d eta u hu ho hd i).symm
  unfold Certificate.prefixShape
  change ((List.range (eta.rowLens.length + (encode T).length)).map
    (fun i => eta.rowLens.getD i 0 + (u.filter (fun b => b.1 == i)).length)).filter
      (fun n => n != 0) = d.rowLens
  simp only [getD_rowLens, hrow]
  exact rowLens_from_bound d _ hbound

/-- Literal certificate-list version. Positivity is used explicitly to remove
the trailing-zero ambiguity of row-length encodings. -/
theorem prefixShape_ofRowLens (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·))
    (hp : ∀ x ∈ eta, 0 < x) (hc : contains nu eta = true)
    (a : StandardTableau (YoungDiagram.ofRowLens eta he))
    (T : SkewStandardTableau (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn))
    (k : ℕ) : Certificate.prefixShape eta (encode T) k =
      (initialDiagram (glueTableau (diagram_le_of_contains eta nu he hn hc) a T).val
        ((YoungDiagram.ofRowLens eta he).card + k)).rowLens := by
  have hh := prefixShape_eq_initialDiagram_rowLens (diagram_le_of_contains eta nu he hn hc) a T k
  simpa only [YoungDiagram.rowLens_ofRowLens_eq_self hp] using hh

theorem contains_of_diagram_le (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·))
    (hp : ∀ x ∈ eta, 0 < x)
    (hle : YoungDiagram.ofRowLens eta he ≤ YoungDiagram.ofRowLens nu hn) : contains nu eta = true := by
  apply (contains_iff eta nu).mpr
  constructor
  · by_contra hh
    have hi : nu.length < eta.length := by omega
    have hv : 0 < eta[nu.length] := hp _ (List.getElem_mem hi)
    have hm : (nu.length, 0) ∈ (YoungDiagram.ofRowLens eta he).cells :=
      YoungDiagram.mem_ofRowLens.mpr ⟨hi, hv⟩
    obtain ⟨hj, _⟩ := YoungDiagram.mem_ofRowLens.mp (hle hm)
    omega
  · intro i hi
    by_contra hh
    have hv : nu.getD i 0 < eta[i] := by omega
    have hm : (i, nu.getD i 0) ∈ (YoungDiagram.ofRowLens eta he).cells :=
      YoungDiagram.mem_ofRowLens.mpr ⟨hi, hv⟩
    have hz := (mem_ofRowLens_iff_getD nu hn (i, nu.getD i 0)).mp (hle hm)
    exact (lt_irrefl _ hz)

theorem contains_iff_diagram_le (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hp : ∀ x ∈ eta, 0 < x) :
    contains nu eta = true ↔ YoungDiagram.ofRowLens eta he ≤ YoungDiagram.ofRowLens nu hn :=
  ⟨diagram_le_of_contains eta nu he hn, contains_of_diagram_le eta nu he hn hp⟩

theorem rowLens_eq_iff_diagram_eq (d : YoungDiagram) (mu : Shape)
    (hm : mu.Sorted (· ≥ ·)) (hp : ∀ x ∈ mu, 0 < x) :
    d.rowLens = mu ↔ d = YoungDiagram.ofRowLens mu hm := by
  constructor
  · intro hh
    apply YoungDiagram.equivListRowLens.injective
    apply Subtype.ext
    change d.rowLens = (YoungDiagram.ofRowLens mu hm).rowLens
    rw [YoungDiagram.rowLens_ofRowLens_eq_self hp, hh]
  · intro hh
    rw [hh, YoungDiagram.rowLens_ofRowLens_eq_self hp]

/-- Exact selector dictionary: list-shape equality is equality of the actual
intermediate straight Young diagram. Both shape canonicality hypotheses are explicit. -/
theorem prefixShape_eq_iff_initialDiagram (eta nu mu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hm : mu.Sorted (· ≥ ·))
    (hep : ∀ x ∈ eta, 0 < x) (hmp : ∀ x ∈ mu, 0 < x) (hc : contains nu eta = true)
    (a : StandardTableau (YoungDiagram.ofRowLens eta he))
    (T : SkewStandardTableau (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn))
    (k : ℕ) : Certificate.prefixShape eta (encode T) k = mu ↔
      initialDiagram (glueTableau (diagram_le_of_contains eta nu he hn hc) a T).val
        ((YoungDiagram.ofRowLens eta he).card + k) = YoungDiagram.ofRowLens mu hm := by
  rw [prefixShape_ofRowLens eta nu he hn hep hc a T k, rowLens_eq_iff_diagram_eq _ mu hm hmp]

end LiebBridge.Young.CertificatePrefixShape
