import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
Standard Young tableaux as order-preserving numberings of a Young diagram.
This file proves the local geometric facts needed for the seminormal action;
it does not assume any representation-theoretic identity.
-/

namespace LiebBridge.Young

abbrev Cell (d : YoungDiagram) := {b : ℕ × ℕ // b ∈ d.cells}

/-- A standard tableau numbers all cells once, increasingly down and right. -/
structure StandardTableau (d : YoungDiagram) where
  number : Cell d ≃ Fin d.card
  increasing : StrictMono number

def boxContent (b : ℕ × ℕ) : ℤ := (b.2 : ℤ) - (b.1 : ℤ)

namespace StandardTableau

variable {d : YoungDiagram} (t : StandardTableau d)

def entry (i : Fin d.card) : Cell d := t.number.symm i

@[simp] theorem number_entry (i : Fin d.card) : t.number (t.entry i) = i :=
  t.number.apply_symm_apply i

@[simp] theorem entry_number (b : Cell d) : t.entry (t.number b) = b :=
  t.number.symm_apply_apply b

theorem number_lt (a b : Cell d) (hab : a < b) : t.number a < t.number b :=
  t.increasing hab

theorem number_le (a b : Cell d) (hab : a ≤ b) : t.number a ≤ t.number b :=
  t.increasing.monotone hab

/-- Comparable cells carrying consecutive labels are neighboring grid cells. -/
theorem neighboring_of_consecutive (a b : Cell d)
    (hgap : (t.number b : ℕ) = (t.number a : ℕ) + 1) (hab : a ≤ b) :
    (b.1.1 = a.1.1 + 1 ∧ b.1.2 = a.1.2) ∨
      (b.1.1 = a.1.1 ∧ b.1.2 = a.1.2 + 1) := by
  change a.1.1 ≤ b.1.1 ∧ a.1.2 ≤ b.1.2 at hab
  by_cases hr : a.1.1 < b.1.1
  · have hm : (a.1.1 + 1, a.1.2) ∈ d.cells :=
      d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) (by omega) hab.2 b.2
    let c : Cell d := ⟨(a.1.1 + 1, a.1.2), hm⟩
    have hac : a < c := by
      change (a.1.1, a.1.2) < (a.1.1 + 1, a.1.2)
      exact lt_of_le_of_ne (by constructor <;> omega)
        (by intro h; have := congrArg Prod.fst h; omega)
    have hcb : c ≤ b := by change a.1.1 + 1 ≤ b.1.1 ∧ a.1.2 ≤ b.1.2; omega
    have h₁ := t.number_lt a c hac
    have h₂ := t.number_le c b hcb
    have he : t.number c = t.number b := by apply Fin.ext; omega
    have hec : c = b := t.number.injective he
    left
    exact ⟨(congrArg (fun z : Cell d => z.1.1) hec).symm,
      (congrArg (fun z : Cell d => z.1.2) hec).symm⟩
  · have hr' : a.1.1 = b.1.1 := by omega
    have hs : a.1.2 < b.1.2 := by
      by_contra hn
      have he : a = b := Subtype.ext (Prod.ext hr' (by omega))
      have hn : (t.number a : ℕ) = (t.number b : ℕ) :=
        congrArg Fin.val (congrArg t.number he)
      omega
    have hm : (a.1.1, a.1.2 + 1) ∈ d.cells :=
      d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) hab.1 (by omega) b.2
    let c : Cell d := ⟨(a.1.1, a.1.2 + 1), hm⟩
    have hac : a < c := by
      change (a.1.1, a.1.2) < (a.1.1, a.1.2 + 1)
      exact lt_of_le_of_ne (by constructor <;> omega)
        (by intro h; have := congrArg Prod.snd h; omega)
    have hcb : c ≤ b := by change a.1.1 ≤ b.1.1 ∧ a.1.2 + 1 ≤ b.1.2; omega
    have h₁ := t.number_lt a c hac
    have h₂ := t.number_le c b hcb
    have he : t.number c = t.number b := by apply Fin.ext; omega
    have hec : c = b := t.number.injective he
    right
    exact ⟨(congrArg (fun z : Cell d => z.1.1) hec).symm,
      (congrArg (fun z : Cell d => z.1.2) hec).symm⟩

/-- The exceptional diagonal-only cases have axial content difference ±1. -/
theorem content_gap_of_consecutive_comparable (a b : Cell d)
    (hgap : (t.number b : ℕ) = (t.number a : ℕ) + 1) (hab : a ≤ b) :
    boxContent b.1 - boxContent a.1 = 1 ∨
      boxContent b.1 - boxContent a.1 = -1 := by
  obtain h | h := t.neighboring_of_consecutive a b hgap hab <;>
    unfold boxContent <;> omega

/-- Two cells with the same content and increasing labels move strictly down
and strictly right. -/
theorem same_content_coordinates (a b : Cell d)
    (hab : t.number a < t.number b) (hc : boxContent a.1 = boxContent b.1) :
    a.1.1 < b.1.1 ∧ a.1.2 < b.1.2 := by
  have hc' : (a.1.2 : ℤ) - (a.1.1 : ℤ) = (b.1.2 : ℤ) - (b.1.1 : ℤ) := hc
  have hn : ¬ b ≤ a := by
    intro h
    have := t.number_le b a h
    omega
  change ¬ (b.1.1 ≤ a.1.1 ∧ b.1.2 ≤ a.1.2) at hn
  omega

/-- Equal contents require at least two differently numbered intervening
cells. Consequently three consecutive labels have pairwise distinct contents. -/
theorem content_ne_of_label_distance_le_two (a b : Cell d)
    (hab : t.number a < t.number b)
    (hgap : (t.number b : ℕ) ≤ (t.number a : ℕ) + 2) :
    boxContent a.1 ≠ boxContent b.1 := by
  intro hc
  obtain ⟨hr, hs⟩ := t.same_content_coordinates a b hab hc
  have hcm : (a.1.1 + 1, a.1.2) ∈ d.cells :=
    d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) (by omega) (by omega) b.2
  have hem : (a.1.1, a.1.2 + 1) ∈ d.cells :=
    d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) (by omega) (by omega) b.2
  let c : Cell d := ⟨(a.1.1 + 1, a.1.2), hcm⟩
  let e : Cell d := ⟨(a.1.1, a.1.2 + 1), hem⟩
  have hac : a < c := by
    change (a.1.1, a.1.2) < (a.1.1 + 1, a.1.2)
    exact lt_of_le_of_ne (by constructor <;> omega)
      (by intro h; have := congrArg Prod.fst h; omega)
  have hcb : c < b := by
    change (a.1.1 + 1, a.1.2) < b.1
    exact lt_of_le_of_ne (by constructor <;> omega) (by intro h; have := congrArg Prod.snd h; omega)
  have hae : a < e := by
    change (a.1.1, a.1.2) < (a.1.1, a.1.2 + 1)
    exact lt_of_le_of_ne (by constructor <;> omega)
      (by intro h; have := congrArg Prod.snd h; omega)
  have heb : e < b := by
    change (a.1.1, a.1.2 + 1) < b.1
    exact lt_of_le_of_ne (by constructor <;> omega) (by intro h; have := congrArg Prod.fst h; omega)
  have h₁ := t.number_lt a c hac
  have h₂ := t.number_lt c b hcb
  have h₃ := t.number_lt a e hae
  have h₄ := t.number_lt e b heb
  have hn : t.number c = t.number e := by
    apply Fin.ext
    omega
  have heq := t.number.injective hn
  have hrce := congrArg (fun x : Cell d => x.1.1) heq
  dsimp [c, e] at hrce
  omega

/-- Incomparable grid cells have axial distance of absolute value at least two. -/
theorem content_gap_of_incomparable (a b : Cell d)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    2 ≤ boxContent b.1 - boxContent a.1 ∨
      boxContent b.1 - boxContent a.1 ≤ -2 := by
  change ¬ (a.1.1 ≤ b.1.1 ∧ a.1.2 ≤ b.1.2) at hab
  change ¬ (b.1.1 ≤ a.1.1 ∧ b.1.2 ≤ a.1.2) at hba
  unfold boxContent
  omega

/-- Swappability of consecutive labels is detected by the two exceptional
axial distances. This is a geometric statement, without a matrix assumption. -/
theorem consecutive_incomparable_iff (a b : Cell d)
    (hgap : (t.number b : ℕ) = (t.number a : ℕ) + 1) :
    (¬ a ≤ b) ↔
      (boxContent b.1 - boxContent a.1 ≠ 1 ∧
       boxContent b.1 - boxContent a.1 ≠ -1) := by
  constructor
  · intro hab
    have hba : ¬ b ≤ a := by
      intro h
      have := t.number_le b a h
      omega
    have h := content_gap_of_incomparable a b hab hba
    omega
  · intro h hab
    have := t.content_gap_of_consecutive_comparable a b hgap hab
    omega

end StandardTableau

end LiebBridge.Young
