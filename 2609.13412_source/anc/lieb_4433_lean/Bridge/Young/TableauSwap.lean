import Bridge.Young.TableauGeometry
import Mathlib.GroupTheory.Perm.Basic

namespace LiebBridge.Young

namespace StandardTableau

variable {d : YoungDiagram}

@[ext] theorem ext {s t : StandardTableau d} (h : s.number = t.number) : s = t := by
  cases s
  cases t
  cases h
  rfl

instance : Finite (StandardTableau d) :=
  Finite.of_injective (fun t : StandardTableau d => t.number) (fun _ _ => ext)

noncomputable instance : Fintype (StandardTableau d) := Fintype.ofFinite _

/-- Swapping neighboring values in a strictly increasing numbering preserves
strict increase if their two cells are incomparable. -/
theorem strictMono_swap_consecutive {α : Type*} [PartialOrder α] {n : ℕ}
    (e : α → Fin n) (he : StrictMono e) (i j : Fin n)
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hinc : ∀ a b, e a = i → e b = j → ¬ a < b) :
    StrictMono (fun a => Equiv.swap i j (e a)) := by
  intro a b hab
  have h := he hab
  have hn : ¬ (e a = i ∧ e b = j) := by
    rintro ⟨hai, hbj⟩
    exact hinc a b hai hbj hab
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

/-- The standard tableau obtained by an allowed adjacent swap. -/
def swapAllowed (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    StandardTableau d where
  number := t.number.trans (Equiv.swap i j)
  increasing := strictMono_swap_consecutive t.number t.increasing i j hij (by
    intro a b hai hbj hab
    have ha : a = t.entry i := t.number.injective (by simpa using hai)
    have hb : b = t.entry j := t.number.injective (by simpa using hbj)
    exact hs (ha ▸ hb ▸ hab.le))

theorem swapAllowed_number (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    (t.swapAllowed i j hij hs).number = t.number.trans (Equiv.swap i j) := rfl

@[simp] theorem swapAllowed_entry (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) (k : Fin d.card) :
    (t.swapAllowed i j hij hs).entry k = t.entry (Equiv.swap i j k) := by
  rfl

theorem reverse_not_le (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) : ¬ t.entry j ≤ t.entry i := by
  intro h
  have hn := t.number_le _ _ h
  simp only [number_entry] at hn
  omega

theorem swapAllowed_swappable (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    ¬ (t.swapAllowed i j hij hs).entry i ≤ (t.swapAllowed i j hij hs).entry j := by
  simpa only [swapAllowed_entry, Equiv.swap_apply_left, Equiv.swap_apply_right]
    using t.reverse_not_le i j hij

/-- Total tableau involution: keep a tableau fixed when the swap is forbidden. -/
def adjacentSwap (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) : StandardTableau d :=
  if hs : ¬ t.entry i ≤ t.entry j then t.swapAllowed i j hij hs else t

theorem adjacentSwap_of_allowed (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    t.adjacentSwap i j hij = t.swapAllowed i j hij hs := dif_pos hs

theorem adjacentSwap_of_forbidden (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : t.entry i ≤ t.entry j) :
    t.adjacentSwap i j hij = t := dif_neg (not_not.mpr hs)

theorem adjacentSwap_involutive (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    Function.Involutive (fun t : StandardTableau d => t.adjacentSwap i j hij) := by
  intro t
  change (t.adjacentSwap i j hij).adjacentSwap i j hij = t
  by_cases hs : ¬ t.entry i ≤ t.entry j
  · rw [adjacentSwap_of_allowed _ _ _ _ hs,
      adjacentSwap_of_allowed _ _ _ _ (t.swapAllowed_swappable i j hij hs)]
    apply ext
    apply Equiv.ext
    intro b
    simp [swapAllowed]
  · have hf : t.entry i ≤ t.entry j := not_not.mp hs
    rw [adjacentSwap_of_forbidden _ _ _ _ hf,
      adjacentSwap_of_forbidden _ _ _ _ hf]

theorem adjacentSwap_entry_other (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (k : Fin d.card) (hki : k ≠ i) (hkj : k ≠ j) :
    (t.adjacentSwap i j hij).entry k = t.entry k := by
  by_cases hs : ¬ t.entry i ≤ t.entry j
  · rw [adjacentSwap_of_allowed _ _ _ _ hs, swapAllowed_entry]
    simp [Equiv.swap_apply_def, hki, hkj]
  · rw [adjacentSwap_of_forbidden _ _ _ _ (not_not.mp hs)]

theorem swaps_commute {α : Type*} [DecidableEq α] (i j p q : α)
    (hpi : p ≠ i) (hpj : p ≠ j) (hqi : q ≠ i) (hqj : q ≠ j) :
    Equiv.swap i j * Equiv.swap p q = Equiv.swap p q * Equiv.swap i j := by
  have hip := hpi.symm
  have hjp := hpj.symm
  have hiq := hqi.symm
  have hjq := hqj.symm
  ext x
  by_cases hxi : x = i
  · subst x; simp_all [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hxj : x = j
  · subst x; simp_all [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hxp : x = p
  · subst x; simp_all [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  by_cases hxq : x = q
  · subst x; simp_all [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  simp_all [Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- Allowed disjoint adjacent swaps commute as actual standard tableaux. -/
theorem adjacentSwap_commute (t : StandardTableau d) (i j p q : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hpq : (q : ℕ) = (p : ℕ) + 1)
    (hpi : p ≠ i) (hpj : p ≠ j) (hqi : q ≠ i) (hqj : q ≠ j) :
    (t.adjacentSwap i j hij).adjacentSwap p q hpq =
      (t.adjacentSwap p q hpq).adjacentSwap i j hij := by
  have he₁ : ((t.adjacentSwap i j hij).entry p ≤
      (t.adjacentSwap i j hij).entry q) ↔ t.entry p ≤ t.entry q := by
    rw [adjacentSwap_entry_other _ _ _ _ _ hpi hpj,
      adjacentSwap_entry_other _ _ _ _ _ hqi hqj]
  have he₂ : ((t.adjacentSwap p q hpq).entry i ≤
      (t.adjacentSwap p q hpq).entry j) ↔ t.entry i ≤ t.entry j := by
    rw [adjacentSwap_entry_other _ _ _ _ _ hpi.symm hqi.symm,
      adjacentSwap_entry_other _ _ _ _ _ hpj.symm hqj.symm]
  by_cases h₁ : ¬ t.entry i ≤ t.entry j <;> by_cases h₂ : ¬ t.entry p ≤ t.entry q
  · have hh₁ : ¬ (t.adjacentSwap i j hij).entry p ≤
        (t.adjacentSwap i j hij).entry q := fun h => h₂ (he₁.mp h)
    have hh₂ : ¬ (t.adjacentSwap p q hpq).entry i ≤
        (t.adjacentSwap p q hpq).entry j := fun h => h₁ (he₂.mp h)
    rw [adjacentSwap_of_allowed _ _ _ _ hh₁,
      adjacentSwap_of_allowed _ _ _ _ hh₂]
    apply ext
    simp only [swapAllowed_number, adjacentSwap_of_allowed _ _ _ _ h₁,
      adjacentSwap_of_allowed _ _ _ _ h₂, swapAllowed_number]
    apply Equiv.ext
    intro b
    have hh := congrArg (fun e : Equiv.Perm (Fin d.card) => e (t.number b))
      (swaps_commute i j p q hpi hpj hqi hqj)
    simpa using hh.symm
  · have hf : (t.adjacentSwap i j hij).entry p ≤
        (t.adjacentSwap i j hij).entry q := he₁.mpr (not_not.mp h₂)
    rw [adjacentSwap_of_forbidden _ _ _ _ hf,
      adjacentSwap_of_forbidden _ _ _ _ (not_not.mp h₂)]
  · have hf : (t.adjacentSwap p q hpq).entry i ≤
        (t.adjacentSwap p q hpq).entry j := he₂.mpr (not_not.mp h₁)
    rw [adjacentSwap_of_forbidden _ _ _ _ hf,
      adjacentSwap_of_forbidden _ _ _ _ (not_not.mp h₁)]
  · simp only [adjacentSwap_of_forbidden _ _ _ _ (not_not.mp h₁),
      adjacentSwap_of_forbidden _ _ _ _ (not_not.mp h₂)]

end StandardTableau

end LiebBridge.Young
