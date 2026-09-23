import Bridge.Young.TableauSwap

/-!
Row and column flags on all numberings of a Young diagram. The rational
seminormal action preserves a subspace and a quotient, rather than the
span of standard numberings as a subspace of all numberings.
-/

namespace LiebBridge.Young

abbrev Numbering (d : YoungDiagram) := Cell d ≃ Fin d.card

def RowIncreasing {d : YoungDiagram} (e : Numbering d) : Prop :=
  ∀ a b : Cell d, a.1.1 = b.1.1 → a.1.2 + 1 = b.1.2 → e a < e b

def ColumnIncreasing {d : YoungDiagram} (e : Numbering d) : Prop :=
  ∀ a b : Cell d, a.1.1 + 1 = b.1.1 → a.1.2 = b.1.2 → e a < e b

theorem rowIncreasing_of_strictMono {d : YoungDiagram} (e : Numbering d)
    (he : StrictMono e) : RowIncreasing e := by
  intro a b hr hc
  apply he
  change a.1 < b.1
  apply lt_of_le_of_ne
  · constructor <;> omega
  · intro h
    have := congrArg Prod.snd h
    omega

theorem columnIncreasing_of_strictMono {d : YoungDiagram} (e : Numbering d)
    (he : StrictMono e) : ColumnIncreasing e := by
  intro a b hr hc
  apply he
  change a.1 < b.1
  apply lt_of_le_of_ne
  · constructor <;> omega
  · intro h
    have := congrArg Prod.fst h
    omega

theorem row_number_le {d : YoungDiagram} (e : Numbering d) (he : RowIncreasing e)
    (a b : Cell d) (hr : a.1.1 = b.1.1) (hc : a.1.2 ≤ b.1.2) : e a ≤ e b := by
  by_cases hh : a.1.2 = b.1.2
  · have h : a = b := Subtype.ext (Prod.ext hr hh)
    rw [h]
  · have hpos : 0 < b.1.2 := by omega
    have hm : (b.1.1, b.1.2 - 1) ∈ d.cells :=
      d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) le_rfl (by omega) b.2
    let c : Cell d := ⟨(b.1.1, b.1.2 - 1), hm⟩
    have hac : e a ≤ e c := row_number_le e he a c hr (by dsimp [c]; omega)
    have hcb : e c < e b := he c b rfl (by dsimp [c]; omega)
    exact hac.trans hcb.le
termination_by b.1.2
decreasing_by omega

theorem column_number_le {d : YoungDiagram} (e : Numbering d)
    (he : ColumnIncreasing e) (a b : Cell d)
    (hr : a.1.1 ≤ b.1.1) (hc : a.1.2 = b.1.2) : e a ≤ e b := by
  by_cases hh : a.1.1 = b.1.1
  · have h : a = b := Subtype.ext (Prod.ext hh hc)
    rw [h]
  · have hpos : 0 < b.1.1 := by omega
    have hm : (b.1.1 - 1, b.1.2) ∈ d.cells :=
      d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) (by omega) le_rfl b.2
    let c : Cell d := ⟨(b.1.1 - 1, b.1.2), hm⟩
    have hac : e a ≤ e c := column_number_le e he a c (by dsimp [c]; omega) hc
    have hcb : e c < e b := he c b (by dsimp [c]; omega) rfl
    exact hac.trans hcb.le
termination_by b.1.1
decreasing_by omega

/-- Neighboring row and column inequalities characterize genuine standard
numberings. This is proved using paths in the Young diagram. -/
theorem strictMono_iff_flags {d : YoungDiagram} (e : Numbering d) :
    StrictMono e ↔ ColumnIncreasing e ∧ RowIncreasing e := by
  constructor
  · intro h
    exact ⟨columnIncreasing_of_strictMono e h, rowIncreasing_of_strictMono e h⟩
  · rintro ⟨hc, hr⟩ a b hab
    have hle : a.1.1 ≤ b.1.1 ∧ a.1.2 ≤ b.1.2 := hab.le
    have hm : (a.1.1, b.1.2) ∈ d.cells :=
      d.up_left_mem (i2 := b.1.1) (j2 := b.1.2) hle.1 le_rfl b.2
    let c : Cell d := ⟨(a.1.1, b.1.2), hm⟩
    have hac : e a ≤ e c := row_number_le e hr a c rfl hle.2
    have hcb : e c ≤ e b := column_number_le e hc c b hle.1 rfl
    exact lt_of_le_of_ne (hac.trans hcb) (fun h => hab.ne (e.injective h))

/-- Adjacent transposition can reverse an increasing pair only by swapping
that very pair of adjacent values. -/
theorem swap_reverses_only_adjacent {n : ℕ} (i j a b : Fin n)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hab : a < b)
    (hrev : ¬ Equiv.swap i j a < Equiv.swap i j b) : a = i ∧ b = j := by
  simp only [Equiv.swap_apply_def] at hrev
  split_ifs at hrev <;> omega

def numberingSwap {d : YoungDiagram} (e : Numbering d) (i j : Fin d.card) :
    Numbering d := e.trans (Equiv.swap i j)

def numberingGap {d : YoungDiagram} (e : Numbering d) (i j : Fin d.card) : ℚ :=
  (boxContent (e.symm j).1 : ℤ) - (boxContent (e.symm i).1 : ℤ)

/-- A transition which breaks a column inequality has zero rational
seminormal off-diagonal coefficient. -/
theorem column_exit_gap {d : YoungDiagram} (e : Numbering d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hc : ColumnIncreasing e) (hbad : ¬ ColumnIncreasing (numberingSwap e i j)) :
    numberingGap e i j = -1 := by
  classical
  simp only [ColumnIncreasing, not_forall] at hbad
  obtain ⟨a, b, hbad⟩ := hbad
  obtain ⟨hr, hs, hn⟩ := hbad
  have hlt := hc a b hr hs
  have hrev : ¬ Equiv.swap i j (e a) < Equiv.swap i j (e b) := hn
  obtain ⟨hai, hbj⟩ := swap_reverses_only_adjacent i j (e a) (e b) hij hlt hrev
  have ha : e.symm i = a := (e.symm_apply_eq).mpr hai.symm
  have hb : e.symm j = b := (e.symm_apply_eq).mpr hbj.symm
  unfold numberingGap
  rw [ha, hb]
  have hz : boxContent b.1 - boxContent a.1 = (-1 : ℤ) := by
    unfold boxContent
    omega
  exact_mod_cast hz

/-- A transition which repairs a row violation also has zero coefficient.
This proves invariance of the row-invalid subspace inside the column flag. -/
theorem row_reentry_gap {d : YoungDiagram} (e : Numbering d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hbad : ¬ RowIncreasing e) (hr : RowIncreasing (numberingSwap e i j)) :
    numberingGap e i j = -1 := by
  classical
  simp only [RowIncreasing, not_forall] at hbad
  obtain ⟨a, b, hbad⟩ := hbad
  obtain ⟨hs, hc, hn⟩ := hbad
  have hne : e a ≠ e b := by
    intro h
    have hb : a.1.2 = b.1.2 := congrArg (fun x : Cell d => x.1.2) (e.injective h)
    omega
  have hlt : e b < e a := by omega
  have hnew := hr a b hs hc
  have hrev : ¬ Equiv.swap i j (e b) < Equiv.swap i j (e a) := by
    change ¬ numberingSwap e i j b < numberingSwap e i j a
    omega
  obtain ⟨hbi, haj⟩ := swap_reverses_only_adjacent i j (e b) (e a) hij hlt hrev
  have ha : e.symm j = a := (e.symm_apply_eq).mpr haj.symm
  have hb : e.symm i = b := (e.symm_apply_eq).mpr hbi.symm
  unfold numberingGap
  rw [ha, hb]
  have hz : boxContent a.1 - boxContent b.1 = (-1 : ℤ) := by
    unfold boxContent
    omega
  exact_mod_cast hz

end LiebBridge.Young
