import Bridge.CertificateAlgorithm
import Bridge.Young.BranchingBasis
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sigma

/-! Structural semantics of the certificate's standard-tableau filter. -/

namespace LiebBridge.Young.CertificateTableaux
open LiebBridge.Certificate
set_option maxRecDepth 10000

def Neighbor (a b : Box) : Prop :=
  (a.1 = b.1 ∧ a.2 + 1 = b.2) ∨ (a.1 + 1 = b.1 ∧ a.2 = b.2)

theorem neighbor_check (t before : Tableau) (coordinate : ℕ) (a : Box) :
    (if coordinate = 0 then true else if t.contains a then before.contains a else true) = true ↔
      coordinate ≠ 0 → a ∈ t → a ∈ before := by
  by_cases h : coordinate = 0 <;> by_cases ha : a ∈ t <;> simp [h, ha]

theorem standard_iff_indexed (t : Tableau) :
    standard t = true ↔ ∀ (i : ℕ) (hi : i < t.length),
      ((t[i]).2 ≠ 0 → ((t[i]).1, (t[i]).2 - 1) ∈ t →
        ((t[i]).1, (t[i]).2 - 1) ∈ t.take i) ∧
      ((t[i]).1 ≠ 0 → ((t[i]).1 - 1, (t[i]).2) ∈ t →
        ((t[i]).1 - 1, (t[i]).2) ∈ t.take i) := by
  simp only [standard, List.all_eq_true, List.forall_mem_zipIdx', Bool.and_eq_true]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact and_congr (neighbor_check t (t.take i) _ _) (neighbor_check t (t.take i) _ _)

local instance : BEq Box := instBEqOfDecidableEq

def NeighborOrdered (t : Tableau) : Prop :=
  ∀ a ∈ t, ∀ b ∈ t, Neighbor a b → t.idxOf a < t.idxOf b

theorem mem_take_iff_idxOf_lt (t : Tableau) (hn : t.Nodup) (a : Box) (ha : a ∈ t) (k : ℕ) :
    a ∈ t.take k ↔ t.idxOf a < k := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : j < t.length := by omega
    have hid := List.idxOf_getElem hn j hj'
    rw [he] at hid
    omega
  · intro hk
    refine ⟨t.idxOf a, ?_, ?_⟩
    · have hl := List.idxOf_lt_length_iff.mpr ha
      omega
    · exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ha)

theorem standard_iff_neighborOrdered (t : Tableau) (hn : t.Nodup) :
    standard t = true ↔ NeighborOrdered t := by
  rw [standard_iff_indexed]
  constructor
  · intro ht a ha b hb hnbr
    have hidx := List.idxOf_lt_length_iff.mpr hb
    have hs := ht (t.idxOf b) hidx
    simp only [List.getElem_idxOf hidx] at hs
    rcases hnbr with ⟨hr, hc⟩ | ⟨hr, hc⟩
    · have hb0 : b.2 ≠ 0 := by omega
      have he : (b.1, b.2 - 1) = a := Prod.ext hr.symm (by omega)
      have hp := hs.1 hb0 (he ▸ ha)
      rw [he] at hp
      exact (mem_take_iff_idxOf_lt t hn a ha _).mp hp
    · have hb0 : b.1 ≠ 0 := by omega
      have he : (b.1 - 1, b.2) = a := Prod.ext (by omega) hc.symm
      have hp := hs.2 hb0 (he ▸ ha)
      rw [he] at hp
      exact (mem_take_iff_idxOf_lt t hn a ha _).mp hp
  · intro ht i hi
    have hb : t[i] ∈ t := List.getElem_mem hi
    constructor
    · intro hz ha
      apply (mem_take_iff_idxOf_lt t hn _ ha i).mpr
      have hh := ht _ ha _ hb (Or.inl ⟨rfl, by omega⟩)
      simpa only [List.idxOf_getElem hn i hi] using hh
    · intro hz ha
      apply (mem_take_iff_idxOf_lt t hn _ ha i).mpr
      have hh := ht _ ha _ hb (Or.inr ⟨by omega, rfl⟩)
      simpa only [List.idxOf_getElem hn i hi] using hh

def ConvexSupport (t : Tableau) : Prop :=
  ∀ a ∈ t, ∀ b ∈ t, ∀ c : Box, a ≤ c → c ≤ b → c ∈ t

theorem neighbor_lt {a b : Box} (h : Neighbor a b) : a < b := by
  apply lt_of_le_of_ne
  · rcases h with ⟨hr, hc⟩ | ⟨hr, hc⟩ <;> constructor <;> omega
  · intro he
    have hr := congrArg Prod.fst he
    have hc := congrArg Prod.snd he
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem idxOf_le_of_convex (t : Tableau) (hc : ConvexSupport t) (ho : NeighborOrdered t)
    (a b : Box) (ha : a ∈ t) (hb : b ∈ t) (hab : a ≤ b) : t.idxOf a ≤ t.idxOf b := by
  by_cases hcol : a.2 < b.2
  · let c : Box := (b.1, b.2 - 1)
    have hac : a ≤ c := ⟨hab.1, by dsimp [c]; omega⟩
    have hcb : c ≤ b := ⟨le_rfl, by dsimp [c]; omega⟩
    have hcm : c ∈ t := hc a ha b hb c hac hcb
    have hi := idxOf_le_of_convex t hc ho a c ha hcm hac
    have hj := ho c hcm b hb (Or.inl ⟨rfl, by dsimp [c]; omega⟩)
    exact hi.trans hj.le
  · have hcol' : a.2 = b.2 := by have := hab.2; omega
    by_cases hrow : a.1 < b.1
    · let c : Box := (b.1 - 1, b.2)
      have hac : a ≤ c := ⟨by dsimp [c]; omega, by dsimp [c]; omega⟩
      have hcb : c ≤ b := ⟨by dsimp [c]; omega, le_rfl⟩
      have hcm : c ∈ t := hc a ha b hb c hac hcb
      have hi := idxOf_le_of_convex t hc ho a c ha hcm hac
      have hj := ho c hcm b hb (Or.inr ⟨by dsimp [c]; omega, rfl⟩)
      exact hi.trans hj.le
    · have he : a = b := Prod.ext (by have := hab.1; omega) hcol'
      rw [he]
termination_by b.1 + b.2
decreasing_by all_goals omega

/-- The numbering is the inverse of the duplicate-free list of boxes. -/
def listNumbering (t : Tableau) (hn : t.Nodup) : {b // b ∈ t} ≃ Fin t.length :=
  (List.Nodup.getEquiv t hn).symm

@[simp] theorem listNumbering_val (t : Tableau) (hn : t.Nodup) (b : {b // b ∈ t}) :
    (listNumbering t hn b).val = t.idxOf b.val := rfl

/-- On a convex set of grid cells, the certificate's exact neighbor filter is
equivalent to an increasing numbering of the inherited grid order. -/
theorem standard_iff_strictMono (t : Tableau) (hn : t.Nodup) (hc : ConvexSupport t) :
    standard t = true ↔ StrictMono (listNumbering t hn) := by
  rw [standard_iff_neighborOrdered t hn]
  constructor
  · intro ho a b hab
    change t.idxOf a.val < t.idxOf b.val
    apply lt_of_le_of_ne (idxOf_le_of_convex t hc ho _ _ a.property b.property hab.le)
    intro he
    exact hab.ne (Subtype.ext ((List.idxOf_inj a.property b.property).mp he))
  · intro hm a ha b hb hab
    exact hm (show (⟨a, ha⟩ : {b // b ∈ t}) < ⟨b, hb⟩ from neighbor_lt hab)

/-- Skew Young diagrams satisfy precisely the convex-support hypothesis used
above: an interval between two skew cells remains in the skew diagram. -/
theorem convexSupport_of_skew (eta nu : YoungDiagram) (t : Tableau)
    (hm : ∀ b : Box, b ∈ t ↔ b ∈ nu.cells ∧ b ∉ eta.cells) : ConvexSupport t := by
  intro a ha b hb c hac hcb
  apply (hm c).mpr
  refine ⟨nu.isLowerSet hcb ((hm b).mp hb).1, ?_⟩
  intro hce
  exact ((hm a).mp ha).2 (eta.isLowerSet hac hce)

theorem standard_iff_strictMono_on_skew (eta nu : YoungDiagram) (t : Tableau)
    (hn : t.Nodup) (hm : ∀ b : Box, b ∈ t ↔ b ∈ nu.cells ∧ b ∉ eta.cells) :
    standard t = true ↔ StrictMono (listNumbering t hn) :=
  standard_iff_strictMono t hn (convexSupport_of_skew eta nu t hm)

theorem mem_skewBoxes_iff (eta nu : Shape) (b : Box) :
    b ∈ skewBoxes eta nu ↔
      ∃ hi : b.1 < nu.length, b.2 < nu[b.1] ∧ eta.getD b.1 0 ≤ b.2 := by
  simp only [skewBoxes, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  rw [List.exists_mem_zipIdx']
  constructor
  · rintro ⟨i, hi, j, ⟨hj, he⟩, hb⟩
    subst b
    exact ⟨hi, hj, he⟩
  · rintro ⟨hi, hj, he⟩
    exact ⟨b.1, hi, b.2, ⟨hj, he⟩, rfl⟩

theorem mem_ofRowLens_iff_getD (s : Shape) (hs : s.Sorted (· ≥ ·)) (b : Box) :
    b ∈ (YoungDiagram.ofRowLens s hs).cells ↔ b.2 < s.getD b.1 0 := by
  change b ∈ YoungDiagram.ofRowLens s hs ↔ _
  rw [YoungDiagram.mem_ofRowLens]
  by_cases hi : b.1 < s.length
  · simp [hi, List.getD_eq_getElem s 0 hi]
  · rw [List.getD_eq_default s 0 (n := b.1) (by omega)]
    simp [hi]

theorem mem_skewBoxes_diagram (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (b : Box) :
    b ∈ skewBoxes eta nu ↔ b ∈ (YoungDiagram.ofRowLens nu hn).cells ∧
      b ∉ (YoungDiagram.ofRowLens eta he).cells := by
  rw [mem_skewBoxes_iff, mem_ofRowLens_iff_getD, mem_ofRowLens_iff_getD]
  constructor
  · rintro ⟨hi, hb, he⟩
    rw [List.getD_eq_getElem nu 0 hi]
    exact ⟨hb, by omega⟩
  · rintro ⟨hb, he⟩
    have hi : b.1 < nu.length := by
      by_contra hh
      rw [List.getD_eq_default nu 0 (by omega)] at hb
      omega
    refine ⟨hi, ?_, by omega⟩
    simpa only [List.getD_eq_getElem nu 0 hi] using hb

theorem skewBoxes_nodup (eta nu : Shape) : (skewBoxes eta nu).Nodup := by
  unfold skewBoxes
  rw [List.nodup_flatMap]
  constructor
  · intro p hp
    apply List.Nodup.map (fun a b hab => (Prod.mk.inj hab).2)
    exact List.Nodup.filter _ List.nodup_range
  · have hp : nu.zipIdx.Pairwise (fun p q => p.2 ≠ q.2) :=
      List.pairwise_map.mp (List.nodup_zipIdx_map_snd nu)
    apply hp.imp
    intro p q hne
    apply List.disjoint_left.mpr
    intro b hb hc
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hb
    obtain ⟨k, hk, hf⟩ := List.mem_map.mp hc
    exact hne ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)

/-- The actual finite tableau enumerator has no duplicate basis vectors for
any input shapes, proved from its permutation construction. -/
theorem tableaux_nodup (eta nu : Shape) : (tableaux eta nu).Nodup := by
  unfold tableaux
  split_ifs
  · apply List.Nodup.filter
    exact (List.permutations_perm_permutations' _).nodup_iff.mp
      (List.nodup_permutations _ (skewBoxes_nodup eta nu))
  · simp

theorem mem_tableaux_iff (eta nu : Shape) (t : Tableau) :
    t ∈ tableaux eta nu ↔ contains nu eta = true ∧ t.Perm (skewBoxes eta nu) ∧ standard t = true := by
  unfold tableaux
  split_ifs with hc
  · simp [hc, List.mem_permutations']
  · simp [hc]

/-- Semantic soundness and completeness of the exact filter on every
permutation of the certificate's actual skew-box list. -/
theorem standard_permutation_iff_strictMono (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (t : Tableau)
    (hp : t.Perm (skewBoxes eta nu)) :
    standard t = true ↔ StrictMono (listNumbering t (hp.nodup_iff.mpr (skewBoxes_nodup eta nu))) := by
  apply standard_iff_strictMono_on_skew (YoungDiagram.ofRowLens eta he) (YoungDiagram.ofRowLens nu hn)
  intro b
  exact hp.mem_iff.trans (mem_skewBoxes_diagram eta nu he hn b)

/-- Exact semantic characterization of membership in the unchanged certificate
enumerator. The numbering has the list's length; identifying that length with
the skew-diagram cardinality is a separate dictionary step. -/
theorem mem_tableaux_iff_increasing_numbering (eta nu : Shape)
    (he : eta.Sorted (· ≥ ·)) (hn : nu.Sorted (· ≥ ·)) (t : Tableau) :
    t ∈ tableaux eta nu ↔ contains nu eta = true ∧
      ∃ hp : t.Perm (skewBoxes eta nu),
        StrictMono (listNumbering t (hp.nodup_iff.mpr (skewBoxes_nodup eta nu))) := by
  rw [mem_tableaux_iff]
  constructor
  · rintro ⟨hc, hp, hs⟩
    exact ⟨hc, hp, (standard_permutation_iff_strictMono eta nu he hn t hp).mp hs⟩
  · rintro ⟨hc, hp, hs⟩
    exact ⟨hc, hp, (standard_permutation_iff_strictMono eta nu he hn t hp).mpr hs⟩

end LiebBridge.Young.CertificateTableaux
