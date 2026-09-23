import Bridge.Young.CertificateTableaux
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-! The exact list/numbering dictionary for standard skew tableaux. -/

noncomputable section
namespace LiebBridge.Young.CertificateSkewEquiv
open LiebBridge.Certificate CertificateTableaux
attribute [local instance] Classical.propDecidable
local instance : BEq Box := instBEqOfDecidableEq

variable {eta nu : YoungDiagram}

def SupportMatch (eta nu : YoungDiagram) (t : Tableau) : Prop :=
  ∀ b : Box, b ∈ t ↔ b ∈ nu.cells ∧ b ∉ eta.cells

def skewCellSdiff (eta nu : YoungDiagram) : SkewCell eta nu ≃ ↥(nu.cells \ eta.cells) where
  toFun b := ⟨b.val.val, Finset.mem_sdiff.mpr ⟨b.val.property, b.property⟩⟩
  invFun b := ⟨⟨b.val, (Finset.mem_sdiff.mp b.property).1⟩, (Finset.mem_sdiff.mp b.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem skewCell_card (h : eta ≤ nu) : Nat.card (SkewCell eta nu) = nu.card - eta.card := by
  rw [Nat.card_congr (skewCellSdiff eta nu)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Finset.card_sdiff h

def skewCellList (t : Tableau) (hm : SupportMatch eta nu t) : SkewCell eta nu ≃ {b // b ∈ t} where
  toFun b := ⟨b.val.val, (hm _).mpr ⟨b.val.property, b.property⟩⟩
  invFun b := ⟨⟨b.val, ((hm _).mp b.property).1⟩, ((hm _).mp b.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem length_of_support (h : eta ≤ nu) (t : Tableau) (hn : t.Nodup)
    (hm : SupportMatch eta nu t) : t.length = nu.card - eta.card := by
  calc
    t.length = Nat.card {b // b ∈ t} := by
      rw [Nat.card_congr (listNumbering t hn)]
      simp
    _ = Nat.card (SkewCell eta nu) := (Nat.card_congr (skewCellList t hm)).symm
    _ = nu.card - eta.card := skewCell_card h

def decode (h : eta ≤ nu) (t : Tableau) (hn : t.Nodup) (hm : SupportMatch eta nu t)
    (hs : standard t = true) : SkewStandardTableau eta nu where
  number := ((skewCellList t hm).trans (listNumbering t hn)).trans
    (finCongr (length_of_support h t hn hm))
  increasing := by
    intro a b hab
    change t.idxOf a.val.val < t.idxOf b.val.val
    exact ((standard_iff_strictMono_on_skew eta nu t hn hm).mp hs)
      (show (skewCellList t hm a) < (skewCellList t hm b) from hab)

@[simp] theorem decode_number_val (h : eta ≤ nu) (t : Tableau) (hn : t.Nodup)
    (hm : SupportMatch eta nu t) (hs : standard t = true) (b : SkewCell eta nu) :
    ((decode h t hn hm hs).number b).val = t.idxOf b.val.val := rfl

def encode (T : SkewStandardTableau eta nu) : Tableau :=
  List.ofFn fun i => ((T.number.symm i).val).val

@[simp] theorem encode_length (T : SkewStandardTableau eta nu) :
    (encode T).length = nu.card - eta.card := List.length_ofFn

theorem encode_getD (T : SkewStandardTableau eta nu) (i : Fin (nu.card - eta.card)) :
    (encode T).getD i.val (0, 0) = (T.number.symm i).val.val := by
  rw [List.getD_eq_getElem (encode T) (0, 0) (by rw [encode_length]; exact i.isLt)]
  simp [encode]

theorem encode_nodup (T : SkewStandardTableau eta nu) : (encode T).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply T.number.symm.injective
  exact Subtype.ext (Subtype.ext hij)

theorem encode_support (T : SkewStandardTableau eta nu) : SupportMatch eta nu (encode T) := by
  intro b
  simp only [encode, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(T.number.symm i).val.property, (T.number.symm i).property⟩
  · rintro ⟨hn, he⟩
    exact ⟨T.number ⟨⟨b, hn⟩, he⟩, by simp⟩

theorem encode_idxOf (T : SkewStandardTableau eta nu) (b : SkewCell eta nu) :
    (encode T).idxOf b.val.val = (T.number b).val := by
  have hi : (T.number b).val < (encode T).length := by rw [encode_length]; exact (T.number b).isLt
  have hh := List.idxOf_getElem (encode_nodup T) (T.number b).val hi
  have he : (encode T)[(T.number b).val] = b.val.val := by simp [encode]
  simpa only [he] using hh

theorem encode_standard (T : SkewStandardTableau eta nu) : standard (encode T) = true := by
  apply (standard_iff_strictMono_on_skew eta nu (encode T) (encode_nodup T) (encode_support T)).mpr
  intro a b hab
  let ca := (skewCellList (encode T) (encode_support T)).symm a
  let cb := (skewCellList (encode T) (encode_support T)).symm b
  change (encode T).idxOf ca.val.val < (encode T).idxOf cb.val.val
  rw [encode_idxOf, encode_idxOf]
  exact T.increasing (show ca < cb from hab)

theorem skew_ext {S T : SkewStandardTableau eta nu} (h : S.number = T.number) : S = T := by
  cases S
  cases T
  cases h
  rfl

@[simp] theorem decode_encode (h : eta ≤ nu) (T : SkewStandardTableau eta nu) :
    decode h (encode T) (encode_nodup T) (encode_support T) (encode_standard T) = T := by
  apply skew_ext
  apply Equiv.ext
  intro b
  apply Fin.ext
  exact encode_idxOf T b

theorem encode_decode (h : eta ≤ nu) (t : Tableau) (hn : t.Nodup)
    (hm : SupportMatch eta nu t) (hs : standard t = true) : encode (decode h t hn hm hs) = t := by
  apply List.ext_getElem
  · rw [encode_length, length_of_support h t hn hm]
  · intro i hi ht
    let b : SkewCell eta nu :=
      (skewCellList t hm).symm ⟨t[i], List.getElem_mem ht⟩
    let j : Fin (nu.card - eta.card) := ⟨i, by simpa only [encode_length] using hi⟩
    have hj : (decode h t hn hm hs).number b = j := by
      apply Fin.ext
      change t.idxOf t[i] = i
      exact List.idxOf_getElem hn i ht
    have hb : (decode h t hn hm hs).number.symm j = b := by
      rw [← hj, Equiv.symm_apply_apply]
    simp only [encode, List.getElem_ofFn]
    change (((decode h t hn hm hs).number.symm j).val).val = t[i]
    rw [hb]
    rfl

def GeometricLists (eta nu : YoungDiagram) :=
  {t : Tableau // t.Nodup ∧ SupportMatch eta nu t ∧ standard t = true}

/-- The actual bijection between box-list linear extensions and standard skew
numberings, including the exact cardinality cast and both inverse laws. -/
def geometricEquiv (h : eta ≤ nu) : GeometricLists eta nu ≃ SkewStandardTableau eta nu where
  toFun t := decode h t.val t.property.1 t.property.2.1 t.property.2.2
  invFun T := ⟨encode T, encode_nodup T, encode_support T, encode_standard T⟩
  left_inv t := Subtype.ext (encode_decode h t.val t.property.1 t.property.2.1 t.property.2.2)
  right_inv := decode_encode h

theorem contains_iff (eta nu : Shape) : contains nu eta = true ↔
    eta.length ≤ nu.length ∧ ∀ (i : ℕ) (hi : i < eta.length), eta[i] ≤ nu.getD i 0 := by
  simp only [contains, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.forall_mem_zipIdx']

theorem diagram_le_of_contains (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true) :
    YoungDiagram.ofRowLens eta he ≤ YoungDiagram.ofRowLens nu hn := by
  intro b hb
  obtain ⟨hi, hb'⟩ := YoungDiagram.mem_ofRowLens.mp hb
  apply (mem_ofRowLens_iff_getD nu hn b).mpr
  exact hb'.trans_le (((contains_iff eta nu).mp hc).2 b.1 hi)

def certificateListsEquiv (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true) :
    {t : Tableau // t ∈ tableaux eta nu} ≃
      GeometricLists (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn) where
  toFun t := by
    have ht := (mem_tableaux_iff eta nu t.val).mp t.property
    refine ⟨t.val, ht.2.1.nodup_iff.mpr (skewBoxes_nodup eta nu), ?_, ht.2.2⟩
    intro b
    exact ht.2.1.mem_iff.trans (mem_skewBoxes_diagram eta nu he hn b)
  invFun t := by
    have hp : t.val.Perm (skewBoxes eta nu) :=
      (List.perm_ext_iff_of_nodup t.property.1 (skewBoxes_nodup eta nu)).mpr
        (fun b => (t.property.2.1 b).trans (mem_skewBoxes_diagram eta nu he hn b).symm)
    exact ⟨t.val, (mem_tableaux_iff eta nu t.val).mpr ⟨hc, hp, t.property.2.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The unchanged certificate tableau list is exactly the genuine standard
skew-tableau basis, with an explicit list-to-numbering inverse construction. -/
def certificateEquiv (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true) :
    {t : Tableau // t ∈ tableaux eta nu} ≃
      SkewStandardTableau (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn) :=
  (certificateListsEquiv eta nu he hn hc).trans
    (geometricEquiv (diagram_le_of_contains eta nu he hn hc))

@[simp] theorem certificateEquiv_symm_val (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true)
    (T : SkewStandardTableau (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn)) :
    ((certificateEquiv eta nu he hn hc).symm T).val = encode T := rfl

theorem encode_certificateEquiv (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true)
    (t : {t : Tableau // t ∈ tableaux eta nu}) :
    encode (certificateEquiv eta nu he hn hc t) = t.val := by
  have hh := congrArg Subtype.val ((certificateEquiv eta nu he hn hc).symm_apply_apply t)
  simpa only [certificateEquiv_symm_val] using hh

theorem certificateEquiv_entry (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true)
    (t : {t : Tableau // t ∈ tableaux eta nu})
    (i : Fin ((YoungDiagram.ofRowLens nu hn).card - (YoungDiagram.ofRowLens eta he).card)) :
    t.val.getD i.val (0, 0) = ((certificateEquiv eta nu he hn hc t).number.symm i).val.val := by
  rw [← encode_certificateEquiv eta nu he hn hc t]
  exact encode_getD _ i

theorem certificateEquiv_content (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true)
    (t : {t : Tableau // t ∈ tableaux eta nu})
    (i : Fin ((YoungDiagram.ofRowLens nu hn).card - (YoungDiagram.ofRowLens eta he).card)) :
    Certificate.content (t.val.getD i.val (0, 0)) =
      boxContent ((certificateEquiv eta nu he hn hc t).number.symm i).val.val := by
  rw [certificateEquiv_entry]
  rfl

end LiebBridge.Young.CertificateSkewEquiv
