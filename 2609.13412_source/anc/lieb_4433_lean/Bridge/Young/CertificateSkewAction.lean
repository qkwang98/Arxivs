import Bridge.Young.CertificateSkewEquiv
import Bridge.Young.TableauSwap
import Bridge.Young.PrefixDecomposition

/-! Transport of the exact list operations to genuine skew numberings and
intermediate straight-tableau prefixes. -/

noncomputable section
namespace LiebBridge.Young.CertificateSkewAction
open LiebBridge.Certificate CertificateSkewEquiv CertificateTableaux
open BranchingBasis PrefixDecomposition StandardTableau
attribute [local instance] Classical.propDecidable
local instance : BEq Box := instBEqOfDecidableEq

theorem ofFn_getD {n : ℕ} (f : Fin n → Box) (i : Fin n) :
    (List.ofFn f).getD i.val (0, 0) = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The unchanged executable swap exchanges exactly the two consecutive
finite-index entries, including every untouched coordinate. -/
theorem swapAdjacent_ofFn {n : ℕ} (f : Fin n → Box) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    Certificate.swapAdjacent (List.ofFn f) i.val = List.ofFn (fun k => f (Equiv.swap i j k)) := by
  apply List.ext_getElem
  · simp [Certificate.swapAdjacent]
  · intro r hr hs
    have hri : r < n := by simpa using hs
    let k : Fin n := ⟨r, hri⟩
    simp only [Certificate.swapAdjacent, List.getElem_mapIdx, List.getElem_ofFn]
    change (if r = i.val then (List.ofFn f).getD (i.val + 1) (0, 0)
      else if r = i.val + 1 then (List.ofFn f).getD i.val (0, 0) else f k) = f (Equiv.swap i j k)
    rw [← hij, ofFn_getD f j, ofFn_getD f i]
    by_cases hi : k = i
    · have hv : r = i.val := congrArg Fin.val hi
      simp [hv, hi]
    by_cases hj : k = j
    · have hv : r = j.val := congrArg Fin.val hj
      have hne : j.val ≠ i.val := by omega
      simp [hv, hj, hne]
    have hi' : r ≠ i.val := fun hh => hi (Fin.ext hh)
    have hj' : r ≠ j.val := fun hh => hj (Fin.ext hh)
    simp [hi', hj', Equiv.swap_apply_of_ne_of_ne hi hj]

variable {eta nu : YoungDiagram}

def swappedTableau (T : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card))
    (hs : StrictMono (T.number.trans (Equiv.swap i j))) : SkewStandardTableau eta nu :=
  ⟨T.number.trans (Equiv.swap i j), hs⟩

theorem encode_swappedTableau (T : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val + 1)
    (hs : StrictMono (T.number.trans (Equiv.swap i j))) :
    encode (swappedTableau T i j hs) = Certificate.swapAdjacent (encode T) i.val := by
  simp only [encode]
  rw [swapAdjacent_ofFn _ i j hij]
  rfl

theorem swap_numbering_strictMono_iff (T : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val + 1) :
    StrictMono (T.number.trans (Equiv.swap i j)) ↔ ¬ T.number.symm i ≤ T.number.symm j := by
  constructor
  · intro hs hle
    have hne : T.number.symm i ≠ T.number.symm j := by
      intro he
      have hij' := T.number.symm.injective he
      have := congrArg Fin.val hij'
      omega
    have hh := hs (lt_of_le_of_ne hle hne)
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right] at hh
    omega
  · intro hs
    apply StandardTableau.strictMono_swap_consecutive T.number T.increasing i j hij
    intro a b hai hbj hab
    have ha : a = T.number.symm i := T.number.injective (by simpa using hai)
    have hb : b = T.number.symm j := T.number.injective (by simpa using hbj)
    exact hs (ha ▸ hb ▸ hab.le)

def numberingList (e : SkewCell eta nu ≃ Fin (nu.card - eta.card)) : Tableau :=
  List.ofFn fun i => (e.symm i).val.val

theorem numberingList_nodup (e : SkewCell eta nu ≃ Fin (nu.card - eta.card)) :
    (numberingList e).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact e.symm.injective (Subtype.ext (Subtype.ext hij))

theorem numberingList_support (e : SkewCell eta nu ≃ Fin (nu.card - eta.card)) :
    SupportMatch eta nu (numberingList e) := by
  intro b
  simp only [numberingList, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(e.symm i).val.property, (e.symm i).property⟩
  · rintro ⟨hn, he⟩
    exact ⟨e ⟨⟨b, hn⟩, he⟩, by simp⟩

theorem numberingList_idxOf (e : SkewCell eta nu ≃ Fin (nu.card - eta.card))
    (b : SkewCell eta nu) : (numberingList e).idxOf b.val.val = (e b).val := by
  have hi : (e b).val < (numberingList e).length := by simp [numberingList]
  have hh := List.idxOf_getElem (numberingList_nodup e) (e b).val hi
  have he : (numberingList e)[(e b).val] = b.val.val := by simp [numberingList]
  simpa only [he] using hh

theorem numberingList_standard_iff (e : SkewCell eta nu ≃ Fin (nu.card - eta.card)) :
    standard (numberingList e) = true ↔ StrictMono e := by
  rw [standard_iff_strictMono_on_skew eta nu (numberingList e)
    (numberingList_nodup e) (numberingList_support e)]
  constructor
  · intro hm a b hab
    have hh := hm (show skewCellList _ (numberingList_support e) a <
        skewCellList _ (numberingList_support e) b from hab)
    change (numberingList e).idxOf a.val.val < (numberingList e).idxOf b.val.val at hh
    simpa only [numberingList_idxOf] using hh
  · intro hm a b hab
    let ca := (skewCellList _ (numberingList_support e)).symm a
    let cb := (skewCellList _ (numberingList_support e)).symm b
    change (numberingList e).idxOf ca.val.val < (numberingList e).idxOf cb.val.val
    rw [numberingList_idxOf, numberingList_idxOf]
    exact hm (show ca < cb from hab)

theorem standard_swapAdjacent_iff (T : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val + 1) :
    standard (Certificate.swapAdjacent (encode T) i.val) = true ↔
      ¬ T.number.symm i ≤ T.number.symm j := by
  have he : Certificate.swapAdjacent (encode T) i.val =
      numberingList (T.number.trans (Equiv.swap i j)) := by
    unfold encode
    rw [swapAdjacent_ofFn _ i j hij]
    rfl
  rw [he, numberingList_standard_iff, swap_numbering_strictMono_iff T i j hij]

/-- The evaluator includes the exchanged basis vector exactly when the
actual adjacent skew-numbering swap is standard. -/
theorem swapAdjacent_mem_tableaux_iff (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (hc : contains nu eta = true)
    (t : {t : Tableau // t ∈ tableaux eta nu})
    (i j : Fin ((YoungDiagram.ofRowLens nu hn).card - (YoungDiagram.ofRowLens eta he).card))
    (hij : j.val = i.val + 1) :
    Certificate.swapAdjacent t.val i.val ∈ tableaux eta nu ↔
      ¬ (certificateEquiv eta nu he hn hc t).number.symm i ≤
        (certificateEquiv eta nu he hn hc t).number.symm j := by
  let T := certificateEquiv eta nu he hn hc t
  have henc : encode T = t.val := encode_certificateEquiv eta nu he hn hc t
  have hlist : Certificate.swapAdjacent (encode T) i.val =
      numberingList (T.number.trans (Equiv.swap i j)) := by
    unfold encode
    rw [swapAdjacent_ofFn _ i j hij]
    rfl
  have hp : (Certificate.swapAdjacent (encode T) i.val).Perm (skewBoxes eta nu) := by
    rw [hlist]
    apply (List.perm_ext_iff_of_nodup (numberingList_nodup _) (skewBoxes_nodup eta nu)).mpr
    intro b
    exact (numberingList_support _ b).trans (mem_skewBoxes_diagram eta nu he hn b).symm
  rw [← henc, mem_tableaux_iff]
  simp only [hc, hp, true_and]
  exact standard_swapAdjacent_iff T i j hij

end LiebBridge.Young.CertificateSkewAction
