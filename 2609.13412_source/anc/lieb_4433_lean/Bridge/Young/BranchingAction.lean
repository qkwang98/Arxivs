import Bridge.Young.BranchingBasis
import Bridge.Young.Seminormal

/-! The actual prefix generators respect the combinatorial prefix basis split.
The intertwining is proved on rational coordinate functions from the concrete
seminormal formula; no representation branching rule is assumed. -/

noncomputable section
namespace LiebBridge.Young.BranchingAction
open BranchingBasis StandardTableau
attribute [local instance] Classical.propDecidable

variable {eta nu : YoungDiagram}

def prefixIndex (h : eta ≤ nu) (i : Fin eta.card) : Fin nu.card :=
  Fin.castLE (card_le h) i

@[simp] theorem prefixIndex_val (h : eta ≤ nu) (i : Fin eta.card) :
    (prefixIndex h i).val = i.val := rfl

theorem prefixIndex_injective (h : eta ≤ nu) : Function.Injective (prefixIndex h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun k : Fin nu.card => k.val) hij

theorem inner_number_embed (h : eta ≤ nu) (t : PrefixTableau eta nu) (b : Cell eta) :
    prefixIndex h ((innerTableau h t).number b) = t.val.number (innerCell h b) := by
  apply Fin.ext
  rfl

theorem inner_entry_embed (h : eta ≤ nu) (t : PrefixTableau eta nu) (i : Fin eta.card) :
    innerCell h ((innerTableau h t).entry i) = t.val.entry (prefixIndex h i) := by
  apply t.val.number.injective
  rw [← inner_number_embed, number_entry, number_entry]

theorem inner_entry_val (h : eta ≤ nu) (t : PrefixTableau eta nu) (i : Fin eta.card) :
    ((innerTableau h t).entry i).val = (t.val.entry (prefixIndex h i)).val :=
  congrArg Subtype.val (inner_entry_embed h t i)

theorem inner_entry_le_iff (h : eta ≤ nu) (t : PrefixTableau eta nu) (i j : Fin eta.card) :
    (innerTableau h t).entry i ≤ (innerTableau h t).entry j ↔
      t.val.entry (prefixIndex h i) ≤ t.val.entry (prefixIndex h j) := by
  change ((innerTableau h t).entry i).val ≤ ((innerTableau h t).entry j).val ↔ _
  rw [inner_entry_val, inner_entry_val]
  rfl

theorem axial_prefix (h : eta ≤ nu) (t : PrefixTableau eta nu) (i j : Fin eta.card) :
    t.val.axial (prefixIndex h i) (prefixIndex h j) = (innerTableau h t).axial i j := by
  simp only [axial, rationalContent, inner_entry_val]

theorem hasPrefix_adjacentSwap_iff (h : eta ≤ nu) (t : StandardTableau nu)
    (i j : Fin eta.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    HasPrefix eta (t.adjacentSwap (prefixIndex h i) (prefixIndex h j) hij) ↔ HasPrefix eta t := by
  by_cases hs : ¬ t.entry (prefixIndex h i) ≤ t.entry (prefixIndex h j)
  · rw [adjacentSwap_of_allowed _ _ _ _ hs]
    have hlabel (b : Cell nu) :
        ((t.swapAllowed (prefixIndex h i) (prefixIndex h j) hij hs).number b).val < eta.card ↔
          (t.number b).val < eta.card := by
      simp only [swapAllowed_number, Equiv.trans_apply, Equiv.swap_apply_def]
      split_ifs with hi hj
      · have hb := congrArg Fin.val hi
        simp only [prefixIndex_val] at hb ⊢
        have := i.isLt
        have := j.isLt
        omega
      · have hb := congrArg Fin.val hj
        simp only [prefixIndex_val] at hb ⊢
        have := i.isLt
        have := j.isLt
        omega
      · rfl
    simp only [HasPrefix, hlabel]
  · rw [adjacentSwap_of_forbidden _ _ _ _ (not_not.mp hs)]

def prefixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu) (i j : Fin eta.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) : PrefixTableau eta nu :=
  ⟨t.val.adjacentSwap (prefixIndex h i) (prefixIndex h j) hij,
    (hasPrefix_adjacentSwap_iff h t.val i j hij).mpr t.property⟩

theorem innerTableau_prefixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin eta.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    innerTableau h (prefixSwap h t i j hij) = (innerTableau h t).adjacentSwap i j hij := by
  by_cases hs : ¬ (innerTableau h t).entry i ≤ (innerTableau h t).entry j
  · have hs' : ¬ t.val.entry (prefixIndex h i) ≤ t.val.entry (prefixIndex h j) :=
      fun hh => hs ((inner_entry_le_iff h t i j).mpr hh)
    apply StandardTableau.ext
    apply Equiv.ext
    intro b
    apply prefixIndex_injective h
    rw [inner_number_embed]
    change (t.val.adjacentSwap (prefixIndex h i) (prefixIndex h j) hij).number (innerCell h b) = _
    rw [adjacentSwap_of_allowed _ _ _ _ hs', adjacentSwap_of_allowed _ _ _ _ hs]
    simp only [swapAllowed_number, Equiv.trans_apply]
    rw [← inner_number_embed]
    exact (Function.Injective.map_swap (prefixIndex_injective h) i j
      ((innerTableau h t).number b)).symm
  · have hs' : t.val.entry (prefixIndex h i) ≤ t.val.entry (prefixIndex h j) :=
      (inner_entry_le_iff h t i j).mp (not_not.mp hs)
    have he : prefixSwap h t i j hij = t := by
      apply Subtype.ext
      exact adjacentSwap_of_forbidden _ _ _ _ hs'
    rw [he, adjacentSwap_of_forbidden _ _ _ _ (not_not.mp hs)]

theorem skew_ext {a b : SkewStandardTableau eta nu} (h : a.number = b.number) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem outerTableau_prefixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin eta.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    outerTableau h (prefixSwap h t i j hij) = outerTableau h t := by
  apply skew_ext
  apply Equiv.ext
  intro b
  apply Fin.ext
  rw [outerTableau_number_val, outerTableau_number_val]
  by_cases hs : ¬ t.val.entry (prefixIndex h i) ≤ t.val.entry (prefixIndex h j)
  · have hb := outer_label_ge t b
    have hi : t.val.number b.val ≠ prefixIndex h i := by
      intro he
      have he' := congrArg Fin.val he
      simp only [prefixIndex_val] at he'
      have := i.isLt
      omega
    have hj : t.val.number b.val ≠ prefixIndex h j := by
      intro he
      have he' := congrArg Fin.val he
      simp only [prefixIndex_val] at he'
      have := j.isLt
      omega
    change ((t.val.adjacentSwap (prefixIndex h i) (prefixIndex h j) hij).number b.val).val - eta.card = _
    rw [adjacentSwap_of_allowed _ _ _ _ hs]
    simp [swapAllowed_number, Equiv.swap_apply_def, hi, hj]
  · change ((t.val.adjacentSwap (prefixIndex h i) (prefixIndex h j) hij).number b.val).val - eta.card = _
    rw [adjacentSwap_of_forbidden _ _ _ _ (not_not.mp hs)]

theorem prefixEquiv_prefixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin eta.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    prefixEquiv h (prefixSwap h t i j hij) =
      ((innerTableau h t).adjacentSwap i j hij, outerTableau h t) := by
  change (innerTableau h (prefixSwap h t i j hij), outerTableau h (prefixSwap h t i j hij)) = _
  rw [innerTableau_prefixSwap, outerTableau_prefixSwap]

def extendByZero (v : PrefixTableau eta nu → ℚ) (t : StandardTableau nu) : ℚ :=
  if ht : HasPrefix eta t then v ⟨t, ht⟩ else 0

/-- The original ambient generator, restricted to a prefix coordinate function. -/
def prefixAction (h : eta ≤ nu) (i j : Fin eta.card) (hij : (j : ℕ) = (i : ℕ) + 1)
    (v : PrefixTableau eta nu → ℚ) (t : PrefixTableau eta nu) : ℚ :=
  generator (prefixIndex h i) (prefixIndex h j) hij (extendByZero v) t.val

theorem prefixAction_apply (h : eta ≤ nu) (i j : Fin eta.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (v : PrefixTableau eta nu → ℚ) (t : PrefixTableau eta nu) :
    prefixAction h i j hij v t =
      (t.val.axial (prefixIndex h i) (prefixIndex h j))⁻¹ * v t +
        if ¬ t.val.entry (prefixIndex h i) ≤ t.val.entry (prefixIndex h j) then
          (1 - (t.val.axial (prefixIndex h i) (prefixIndex h j))⁻¹) * v (prefixSwap h t i j hij)
        else 0 := by
  have hp := (hasPrefix_adjacentSwap_iff h t.val i j hij).mpr t.property
  simp only [prefixAction, generator_apply, extendByZero, dif_pos t.property, dif_pos hp]
  rfl

/-- The ambient generator preserves functions supported on the prescribed
prefix block; extension by zero genuinely intertwines the two actions. -/
theorem generator_extendByZero (h : eta ≤ nu) (i j : Fin eta.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (v : PrefixTableau eta nu → ℚ) :
    generator (prefixIndex h i) (prefixIndex h j) hij (extendByZero v) =
      extendByZero (prefixAction h i j hij v) := by
  funext t
  by_cases hp : HasPrefix eta t
  · simp only [extendByZero, dif_pos hp]
    rfl
  · have hp' : ¬ HasPrefix eta
        (t.adjacentSwap (prefixIndex h i) (prefixIndex h j) hij) :=
      fun hh => hp ((hasPrefix_adjacentSwap_iff h t i j hij).mp hh)
    simp [generator_apply, extendByZero, hp, hp']

/-- The inner generator acts on the first coordinate and fixes the skew coordinate. -/
def splitAction (i j : Fin eta.card) (hij : (j : ℕ) = (i : ℕ) + 1)
    (f : StandardTableau eta × SkewStandardTableau eta nu → ℚ)
    (p : StandardTableau eta × SkewStandardTableau eta nu) : ℚ :=
  generator i j hij (fun a => f (a, p.2)) p.1

/-- Actual prefix-generator branching in rational coordinates. -/
theorem prefixEquiv_intertwines (h : eta ≤ nu) (i j : Fin eta.card)
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (f : StandardTableau eta × SkewStandardTableau eta nu → ℚ) :
    prefixAction h i j hij (f ∘ prefixEquiv h) = splitAction i j hij f ∘ prefixEquiv h := by
  funext t
  rw [prefixAction_apply]
  simp only [Function.comp_apply, splitAction, generator_apply, prefixEquiv,
    Equiv.coe_fn_mk, axial_prefix, innerTableau_prefixSwap, outerTableau_prefixSwap]
  simp only [inner_entry_le_iff]

end LiebBridge.Young.BranchingAction
