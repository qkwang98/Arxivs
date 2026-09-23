import Bridge.Young.TableauGeometry
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The actual standard-tableau prefix basis split

Restricting a standard tableau to a prescribed initial Young diagram gives a standard tableau
of that diagram and a standard skew tableau of the remaining cells. This file constructs the
two restrictions and their inverse, rather than assuming a representation branching rule.
-/

namespace LiebBridge.Young

/-- Cells of `nu` outside `eta`, with their inherited grid order. -/
abbrev SkewCell (eta nu : YoungDiagram) := {b : Cell nu // b.val ∉ eta.cells}

/-- An increasing numbering of a skew diagram, starting at zero. -/
structure SkewStandardTableau (eta nu : YoungDiagram) where
  number : SkewCell eta nu ≃ Fin (nu.card - eta.card)
  increasing : StrictMono number

/-- The first `eta.card` numbered cells are exactly the cells of `eta`. -/
def HasPrefix (eta : YoungDiagram) {nu : YoungDiagram} (t : StandardTableau nu) : Prop :=
  ∀ b : Cell nu, (t.number b).val < eta.card ↔ b.val ∈ eta.cells

abbrev PrefixTableau (eta nu : YoungDiagram) :=
  {t : StandardTableau nu // HasPrefix eta t}

namespace BranchingBasis

variable {eta nu : YoungDiagram}

theorem card_le (h : eta ≤ nu) : eta.card ≤ nu.card := Finset.card_le_card h

def innerCell (h : eta ≤ nu) (b : Cell eta) : Cell nu := ⟨b.val, h b.property⟩

private theorem tableau_ext {a b : StandardTableau nu}
    (h : ∀ c, a.number c = b.number c) : a = b := by
  cases a with | mk an ah =>
    cases b with | mk bn bh =>
      have he : an = bn := Equiv.ext h
      cases he
      rfl

private theorem skewTableau_ext {a b : SkewStandardTableau eta nu}
    (h : ∀ c, a.number c = b.number c) : a = b := by
  cases a with | mk an ah =>
    cases b with | mk bn bh =>
      have he : an = bn := Equiv.ext h
      cases he
      rfl

def innerLabel (h : eta ≤ nu) (t : PrefixTableau eta nu) (b : Cell eta) : Fin eta.card :=
  ⟨t.val.number (innerCell h b), (t.property (innerCell h b)).mpr b.property⟩

theorem innerLabel_bijective (h : eta ≤ nu) (t : PrefixTableau eta nu) :
    Function.Bijective (innerLabel h t) := by
  constructor
  · intro a b hab
    have hv := congrArg (fun z : Fin eta.card => z.val) hab
    have he : t.val.number (innerCell h a) = t.val.number (innerCell h b) :=
      Fin.ext hv
    have hc := t.val.number.injective he
    exact Subtype.ext (congrArg (fun z : Cell nu => z.val) hc)
  · intro i
    let j : Fin nu.card := ⟨i.val, lt_of_lt_of_le i.isLt (card_le h)⟩
    let b := t.val.entry j
    have hb : b.val ∈ eta.cells := (t.property b).mp (by simp [b,j])
    refine ⟨⟨b.val, hb⟩, ?_⟩
    apply Fin.ext
    change (t.val.number (innerCell h ⟨b.val,hb⟩)).val = i.val
    have he : innerCell h ⟨b.val,hb⟩ = b := Subtype.ext rfl
    rw [he]
    simp [b,j]

/-- Restriction to the initial diagram, preserving its labels. -/
noncomputable def innerTableau (h : eta ≤ nu) (t : PrefixTableau eta nu) :
    StandardTableau eta where
  number := Equiv.ofBijective (innerLabel h t) (innerLabel_bijective h t)
  increasing := by
    intro a b hab
    change (t.val.number (innerCell h a)).val < (t.val.number (innerCell h b)).val
    exact t.val.increasing hab

@[simp] theorem innerTableau_number_val (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (b : Cell eta) : ((innerTableau h t).number b).val =
      (t.val.number (innerCell h b)).val := rfl

theorem outer_label_ge (t : PrefixTableau eta nu) (b : SkewCell eta nu) :
    eta.card ≤ (t.val.number b.val).val := by
  have hh : ¬ (t.val.number b.val).val < eta.card := fun hh => b.property ((t.property b.val).mp hh)
  omega

def outerLabel (t : PrefixTableau eta nu) (b : SkewCell eta nu) :
    Fin (nu.card - eta.card) :=
  ⟨(t.val.number b.val).val - eta.card, by
    have hge := outer_label_ge t b
    have hlt := (t.val.number b.val).isLt
    omega⟩

theorem outerLabel_bijective (h : eta ≤ nu) (t : PrefixTableau eta nu) :
    Function.Bijective (outerLabel t) := by
  constructor
  · intro a b hab
    have ha := outer_label_ge t a
    have hb := outer_label_ge t b
    have he := congrArg Fin.val hab
    change (t.val.number a.val).val - eta.card = (t.val.number b.val).val - eta.card at he
    have hn : t.val.number a.val = t.val.number b.val := by apply Fin.ext; omega
    exact Subtype.ext (t.val.number.injective hn)
  · intro i
    let j : Fin nu.card := ⟨eta.card+i.val, by have hi := i.isLt; have hc := card_le h; omega⟩
    let b := t.val.entry j
    have hb : b.val ∉ eta.cells := by
      intro hb
      have hh := (t.property b).mpr hb
      simp [b,j] at hh
    refine ⟨⟨b,hb⟩, ?_⟩
    apply Fin.ext
    change (t.val.number b).val - eta.card = i.val
    simp [b,j]

/-- Restriction to the remaining cells, subtracting the size of the prefix from every label. -/
noncomputable def outerTableau (h : eta ≤ nu) (t : PrefixTableau eta nu) :
    SkewStandardTableau eta nu where
  number := Equiv.ofBijective (outerLabel t) (outerLabel_bijective h t)
  increasing := by
    intro a b hab
    have hh := t.val.increasing hab
    change (t.val.number a.val).val < (t.val.number b.val).val at hh
    have ha := outer_label_ge t a
    have hb := outer_label_ge t b
    change (t.val.number a.val).val - eta.card < (t.val.number b.val).val - eta.card
    omega

@[simp] theorem outerTableau_number_val (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (b : SkewCell eta nu) : ((outerTableau h t).number b).val =
      (t.val.number b.val).val - eta.card := rfl

/-- Partition the actual cells into the initial diagram and its complement. -/
def cellSplit (h : eta ≤ nu) : Cell nu ≃ Cell eta ⊕ SkewCell eta nu :=
  (Equiv.sumCompl (fun b : Cell nu => b.val ∈ eta.cells)).symm.trans
    (Equiv.sumCongr (Equiv.subtypeSubtypeEquivSubtype (fun hb => h hb)) (Equiv.refl _))

/-- Join the two numbering equivalences, shifting every skew label by `eta.card`. -/
def glueNumber (h : eta ≤ nu) (a : StandardTableau eta) (b : SkewStandardTableau eta nu) :
    Cell nu ≃ Fin nu.card :=
  (((cellSplit h).trans (Equiv.sumCongr a.number b.number)).trans finSumFinEquiv).trans
    (finCongr (by have hh := card_le h; omega))

theorem glueNumber_inner (h : eta ≤ nu) (a : StandardTableau eta)
    (b : SkewStandardTableau eta nu) (c : Cell nu) (hc : c.val ∈ eta.cells) :
    (glueNumber h a b c).val = (a.number ⟨c.val,hc⟩).val := by
  simp [glueNumber, cellSplit, hc]
  rfl

theorem glueNumber_outer (h : eta ≤ nu) (a : StandardTableau eta)
    (b : SkewStandardTableau eta nu) (c : Cell nu) (hc : c.val ∉ eta.cells) :
    (glueNumber h a b c).val = eta.card + (b.number ⟨c,hc⟩).val := by
  simp [glueNumber, cellSplit, hc]

theorem glueNumber_increasing (h : eta ≤ nu) (a : StandardTableau eta)
    (b : SkewStandardTableau eta nu) : StrictMono (glueNumber h a b) := by
  intro c d hcd
  change (glueNumber h a b c).val < (glueNumber h a b d).val
  by_cases hc : c.val ∈ eta.cells
  · by_cases hd : d.val ∈ eta.cells
    · rw [glueNumber_inner h a b c hc, glueNumber_inner h a b d hd]
      exact a.increasing hcd
    · rw [glueNumber_inner h a b c hc, glueNumber_outer h a b d hd]
      have hi := (a.number ⟨c.val,hc⟩).isLt
      omega
  · have hd : d.val ∉ eta.cells := by
      intro hd
      exact hc (eta.isLowerSet (show c.val ≤ d.val from le_of_lt hcd) hd)
    rw [glueNumber_outer h a b c hc, glueNumber_outer h a b d hd]
    have hi := b.increasing (show (⟨c,hc⟩ : SkewCell eta nu) < ⟨d,hd⟩ from hcd)
    change (b.number ⟨c,hc⟩).val < (b.number ⟨d,hd⟩).val at hi
    omega

/-- Gluing an initial standard tableau to an independently standard skew tableau. -/
def glueTableau (h : eta ≤ nu) (a : StandardTableau eta)
    (b : SkewStandardTableau eta nu) : PrefixTableau eta nu :=
  ⟨⟨glueNumber h a b, glueNumber_increasing h a b⟩, by
    intro c
    by_cases hc : c.val ∈ eta.cells
    · change (glueNumber h a b c).val < eta.card ↔ c.val ∈ eta.cells
      rw [glueNumber_inner h a b c hc]
      exact iff_of_true (a.number ⟨c.val,hc⟩).isLt hc
    · change (glueNumber h a b c).val < eta.card ↔ c.val ∈ eta.cells
      rw [glueNumber_outer h a b c hc]
      exact iff_of_false (by omega) hc⟩

@[simp] theorem innerTableau_glue (h : eta ≤ nu) (a : StandardTableau eta)
    (b : SkewStandardTableau eta nu) : innerTableau h (glueTableau h a b) = a := by
  apply tableau_ext
  intro c
  apply Fin.ext
  rw [innerTableau_number_val]
  change (glueNumber h a b (innerCell h c)).val = (a.number c).val
  rw [glueNumber_inner h a b (innerCell h c) c.property]
  rfl

@[simp] theorem outerTableau_glue (h : eta ≤ nu) (a : StandardTableau eta)
    (b : SkewStandardTableau eta nu) : outerTableau h (glueTableau h a b) = b := by
  apply skewTableau_ext
  intro c
  apply Fin.ext
  rw [outerTableau_number_val]
  change (glueNumber h a b c.val).val - eta.card = (b.number c).val
  rw [glueNumber_outer h a b c.val c.property]
  simp

@[simp] theorem glue_restrictions (h : eta ≤ nu) (t : PrefixTableau eta nu) :
    glueTableau h (innerTableau h t) (outerTableau h t) = t := by
  apply Subtype.ext
  apply tableau_ext
  intro c
  apply Fin.ext
  change (glueNumber h (innerTableau h t) (outerTableau h t) c).val = (t.val.number c).val
  by_cases hc : c.val ∈ eta.cells
  · rw [glueNumber_inner h _ _ c hc, innerTableau_number_val]
    rfl
  · rw [glueNumber_outer h _ _ c hc, outerTableau_number_val]
    have hh := outer_label_ge t ⟨c,hc⟩
    change eta.card ≤ (t.val.number c).val at hh
    change eta.card + ((t.val.number c).val - eta.card) = (t.val.number c).val
    omega

/-- The actual prefix-tableau basis equivalence.
This is a combinatorial theorem; no representation or branching identity is assumed. -/
noncomputable def prefixEquiv (h : eta ≤ nu) :
    PrefixTableau eta nu ≃ StandardTableau eta × SkewStandardTableau eta nu where
  toFun t := (innerTableau h t, outerTableau h t)
  invFun ab := glueTableau h ab.1 ab.2
  left_inv := glue_restrictions h
  right_inv ab := Prod.ext (innerTableau_glue h ab.1 ab.2) (outerTableau_glue h ab.1 ab.2)

instance finite_standardTableau (d : YoungDiagram) : Finite (StandardTableau d) :=
  Finite.of_injective (fun t : StandardTableau d => t.number)
    (fun _ _ hh => tableau_ext (DFunLike.congr_fun hh))

instance finite_skewStandardTableau (eta nu : YoungDiagram) :
    Finite (SkewStandardTableau eta nu) :=
  Finite.of_injective (fun t : SkewStandardTableau eta nu => t.number)
    (fun _ _ hh => skewTableau_ext (DFunLike.congr_fun hh))

/-- The multiplicity of the prefix basis is the product of the two genuine tableau counts. -/
theorem prefix_card (h : eta ≤ nu) :
    Nat.card (PrefixTableau eta nu) =
      Nat.card (StandardTableau eta) * Nat.card (SkewStandardTableau eta nu) := by
  rw [Nat.card_congr (prefixEquiv h), Nat.card_prod]

/-- The set of cells carrying labels strictly below `k`. -/
def initialCells (t : StandardTableau nu) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ.filter (fun i : Fin nu.card => i.val < k)).image (fun i => (t.entry i).val)

theorem initialCells_subset (t : StandardTableau nu) (k : ℕ) :
    initialCells t k ⊆ nu.cells := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  exact (t.entry i).property

theorem mem_initialCells (t : StandardTableau nu) (k : ℕ) (b : Cell nu) :
    b.val ∈ initialCells t k ↔ (t.number b).val < k := by
  constructor
  · intro hb
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hb
    have hentry : t.entry i = b := Subtype.ext he
    have hnumber : i = t.number b := by rw [← hentry, t.number_entry]
    subst i
    exact (Finset.mem_filter.mp hi).2
  · intro hb
    apply Finset.mem_image.mpr
    exact ⟨t.number b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,
      congrArg Subtype.val (t.entry_number b)⟩

/-- The predicate used in `prefixEquiv` is exactly equality of the first-cell set. -/
theorem hasPrefix_iff_initialCells (h : eta ≤ nu) (t : StandardTableau nu) :
    HasPrefix eta t ↔ initialCells t eta.card = eta.cells := by
  constructor
  · intro ht
    ext b
    by_cases hb : b ∈ nu.cells
    · exact (mem_initialCells t eta.card ⟨b,hb⟩).trans (ht ⟨b,hb⟩)
    · exact iff_of_false (fun hh => hb (initialCells_subset t eta.card hh))
        (fun hh => hb (h hh))
  · intro ht b
    rw [← mem_initialCells t eta.card b, ht]

/-- The same basis split stated literally by equality of the set of prefix cells. -/
noncomputable def prefixCellsEquiv (h : eta ≤ nu) :
    {t : StandardTableau nu // initialCells t eta.card = eta.cells} ≃
      StandardTableau eta × SkewStandardTableau eta nu :=
  (Equiv.subtypeEquivRight (fun t => (hasPrefix_iff_initialCells h t).symm)).trans
    (prefixEquiv h)

theorem prefix_cells_card (h : eta ≤ nu) :
    Nat.card {t : StandardTableau nu // initialCells t eta.card = eta.cells} =
      Nat.card (StandardTableau eta) * Nat.card (SkewStandardTableau eta nu) := by
  rw [Nat.card_congr (prefixCellsEquiv h), Nat.card_prod]

end BranchingBasis

end LiebBridge.Young
