/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung C1 of the article-2 formalisation: the water-filling clamp

Formalisation of Lemma 1, Lemma 2 and Theorem A of
`working-notes/bijective-chaining-greedy-windows.org` (§§0–3) — the
closed-form degreewise clamp of `rem-explicit-inverse` / `eq:water-filling`
in `article/exterior-convex_article2_draft_3.org`, and the injectivity of
the sum map `Φ` on chained tuples that it yields.  Per
`working-notes/PLAN-formalise-article2.org`, rung C1.  Surjectivity (the
note's Lemma W) is deliberately **not** formalised: it is open
combinatorially, and its algebraic proof routes through Amata–Crupi
lex-submodule theory (rung C3, a non-target).

Design decisions, per the plan for this rung:

* **Absolute degrees are indexed by total functions `ℕ → ℕ`**, zero outside
  the supported window, exactly as `Amat` is total on ℤ²: `extN` extends an
  `f`-vector by zero, `shiftAbs dk` places it in absolute degrees
  `dk, …, dk + n`.  No `Fin (N+1)` bookkeeping.  The bridge to article 1's
  ℝ-valued `ffvec` (`Spine/Sumset.lean`) is `ffvec_eq_phi`.
* **Chaining is stated in the absolute form** `t̂_i < ρ̂_{i+1}` of the
  note's §0, where `t̂_i = tp(s⃗_i) + d_i` and `ρ̂_i = indeg(s⃗_i) + d_i`
  (`hatTop`, `hatIndeg`): the gap vector `δ` never appears, and **no
  monotonicity of `d` is needed anywhere** in Lemma 2 or Theorem A.
  `chained_iff_gap` is the dictionary back to the manuscript's printed
  `tp(s⃗_{i-1}) < indeg(s⃗_i) + δ_i` with `δ_i = d_i − d_{i-1} ∈ ℕ`, under
  `Monotone d`; monotonicity is used only in its ⟸ direction.
* **The clamp `Q_i(j) = max(0, x(j) − Σ_{k>i} C_k(j))` is ℕ-truncated
  subtraction** (`Qclamp`): over ℕ, `x - t` *is* `max(0, x − t)`, so the
  note's outer `max(0,·)` is absorbed into the ambient arithmetic.  This
  genuinely collapses the two cases of Theorem A's proof at the level of
  the statement: in the case `j < ρ̂_{c+1}` the subtraction is exact
  (`(y + t) - t = y`), in the case `j > t̂_c` it truncates to zero, which
  is the correct value (`x ≤ t → x - t = 0`).  The case split survives
  only inside the proof of `Qclamp_phi`, as `chained_dichotomy`.

Component indices are 0-based here (`i : Fin r`), against the note's
1-based `i = 1, …, r`; a cut index `c : ℕ` corresponds to the note's
`i = c` in `Q_i`/`y_i`, so `tailC n d c` sums the note's `Σ_{k>c}` and
`headPhi d s c` is the note's `y_c = Σ_{k≤c}`.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`).
-/
import ExteriorConvex.Counting.Stats
import ExteriorConvex.Spine.Sumset

open Finset

namespace ExteriorConvex

/-! ## Lemma 1: profile of a single `f`-vector

For `s⃗ ∈ 𝓕_n` with `ρ = indeg(s⃗)`, `t = tp(s⃗)`:  `s(m) = C(n,m)` for
`m < ρ`; `0 < s(m) < C(n,m)` for `ρ ≤ m ≤ t`; `s(m) = 0` for `m > t`.
The last clause is `Stats.lean`'s `apply_eq_zero_of_top_lt` verbatim and
the first is one `le_antisymm` away from `choose_le_of_lt_indeg`; only the
middle clause is genuinely new, and it is exactly where downward closure
enters, through the two propagation lemmas below. -/

/-- Positivity propagates downward in an order ideal: a `b`-face has
subsets of every smaller cardinality, and they are faces too. -/
theorem fEntry_pos_of_le {n : ℕ} {D : Finset (Finset (Fin n))}
    (hD : IsOrderIdeal D) {a b : ℕ} (hab : a ≤ b) (hb : 0 < fEntry D b) :
    0 < fEntry D a := by
  rw [fEntry, card_pos] at hb ⊢
  obtain ⟨σ, hσ⟩ := hb
  obtain ⟨hσD, hσcard⟩ := mem_filter.mp hσ
  obtain ⟨τ, hτσ, hτcard⟩ := exists_subset_card_eq (show a ≤ #σ by omega)
  exact ⟨τ, mem_filter.mpr ⟨hD hσD hτσ, hτcard⟩⟩

/-- Fullness propagates downward in an order ideal: if every `b`-set is a
face then so is every `a`-set with `a ≤ b ≤ n`, since it extends to a
`b`-set. -/
theorem fEntry_eq_choose_of_le {n : ℕ} {D : Finset (Finset (Fin n))}
    (hD : IsOrderIdeal D) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    (hb : fEntry D b = n.choose b) : fEntry D a = n.choose a := by
  -- every `b`-subset of `[n]` is a face: a full count forces the full set
  have hall : ∀ σ : Finset (Fin n), #σ = b → σ ∈ D := by
    have hsub : D.filter (fun t => #t = b) ⊆
        univ.filter fun t : Finset (Fin n) => #t = b :=
      fun t ht => mem_filter.mpr ⟨mem_univ t, (mem_filter.mp ht).2⟩
    have hcard : #(univ.filter fun t : Finset (Fin n) => #t = b) ≤
        #(D.filter fun t => #t = b) := by
      have h1 : #(univ.filter fun t : Finset (Fin n) => #t = b) =
          n.choose b := fEntry_univ b
      have h2 : #(D.filter fun t => #t = b) = n.choose b := hb
      omega
    have heq := eq_of_subset_of_card_le hsub hcard
    intro σ hσ
    have hmem : σ ∈ D.filter fun t => #t = b := by
      rw [heq]
      exact mem_filter.mpr ⟨mem_univ σ, hσ⟩
    exact (mem_filter.mp hmem).1
  -- hence every `a`-subset is a face, by extension and downward closure
  have hallA : ∀ τ : Finset (Fin n), #τ = a → τ ∈ D := by
    intro τ hτ
    obtain ⟨σ, hτσ, hσcard⟩ := exists_superset_card_eq
      (show #τ ≤ b by omega) (by simpa using hbn)
    exact hD (hall σ hσcard) hτσ
  have hfil : D.filter (fun t => #t = a) =
      univ.filter fun t : Finset (Fin n) => #t = a := by
    ext t
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hallA t h, h⟩⟩
  rw [fEntry, hfil]
  exact fEntry_univ a

/-- The top statistic is attained: if `tp(s⃗) ≥ 0` there is an index at
`tp(s⃗)` with a positive entry.  (No membership in `𝓕_n` needed.) -/
theorem exists_apply_pos_of_top_nonneg {n : ℕ} {s : Fin (n + 1) → ℕ}
    (h : 0 ≤ top s) : ∃ j : Fin (n + 1), (j.val : ℤ) = top s ∧ 0 < s j := by
  rw [top] at h ⊢
  split_ifs at h ⊢ with hne
  · exact ⟨_, rfl, (mem_filter.mp (max'_mem _ hne)).2⟩
  · exact absurd h (by omega)

/-- The initial-degree statistic is attained: if `indeg(s⃗) ≤ n` there is
an index at `indeg(s⃗)` with a strictly sub-binomial entry. -/
theorem exists_apply_lt_choose_of_indeg_le {n : ℕ} {s : Fin (n + 1) → ℕ}
    (h : indeg s ≤ n) :
    ∃ j : Fin (n + 1), j.val = indeg s ∧ s j < n.choose j.val := by
  rw [indeg] at h ⊢
  split_ifs at h ⊢ with hne
  · exact ⟨_, rfl, (mem_filter.mp (min'_mem _ hne)).2⟩
  · exact absurd h (by omega)

/-- Lemma 1, below the window: `s(m) = C(n,m)` for `m < indeg(s⃗)`. -/
theorem apply_eq_choose_of_lt_indeg {n : ℕ} {s : Fin (n + 1) → ℕ}
    (hs : s ∈ Fn n) {m : Fin (n + 1)} (h : m.val < indeg s) :
    s m = n.choose m.val :=
  le_antisymm (apply_le_choose_of_mem_Fn hs m) (choose_le_of_lt_indeg h)

/-- Lemma 1, window, lower half: `0 < s(m)` for `m ≤ tp(s⃗)` — positivity
at the top propagates down by downward closure. -/
theorem apply_pos_of_le_top {n : ℕ} {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n)
    {m : Fin (n + 1)} (h : (m.val : ℤ) ≤ top s) : 0 < s m := by
  obtain ⟨j, hj, hjpos⟩ :=
    exists_apply_pos_of_top_nonneg (le_trans (Int.natCast_nonneg _) h)
  obtain ⟨D, hD, rfl⟩ := mem_Fn.mp hs
  exact fEntry_pos_of_le hD (show m.val ≤ j.val by omega) hjpos

/-- Lemma 1, window, upper half: `s(m) < C(n,m)` for `indeg(s⃗) ≤ m` —
fullness at `m` would propagate down to the witness at `indeg(s⃗)`. -/
theorem apply_lt_choose_of_indeg_le {n : ℕ} {s : Fin (n + 1) → ℕ}
    (hs : s ∈ Fn n) {m : Fin (n + 1)} (h : indeg s ≤ m.val) :
    s m < n.choose m.val := by
  obtain ⟨j, hj, hjlt⟩ :=
    exists_apply_lt_choose_of_indeg_le (le_trans h m.is_le)
  obtain ⟨D, hD, rfl⟩ := mem_Fn.mp hs
  simp only [fvecN_apply] at hjlt ⊢
  by_contra hcon
  have heq : fEntry D m.val = n.choose m.val :=
    le_antisymm (fEntry_le_choose D m.val) (not_lt.mp hcon)
  have := fEntry_eq_choose_of_le hD (show j.val ≤ m.val by omega) m.is_le heq
  omega

/-- **Lemma 1** of the note, packaged: an `f`-vector in `𝓕_n` is the full
binomial below `indeg`, strictly pinched between `0` and the binomial on
the window `[indeg, tp]`, and zero above `tp`. -/
theorem profile_of_mem_Fn {n : ℕ} {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n)
    (m : Fin (n + 1)) :
    (m.val < indeg s → s m = n.choose m.val) ∧
      (indeg s ≤ m.val → (m.val : ℤ) ≤ top s →
        0 < s m ∧ s m < n.choose m.val) ∧
      (top s < (m.val : ℤ) → s m = 0) :=
  ⟨fun h => apply_eq_choose_of_lt_indeg hs h,
   fun h1 h2 => ⟨apply_pos_of_le_top hs h2, apply_lt_choose_of_indeg_le hs h1⟩,
   fun h => apply_eq_zero_of_top_lt h⟩

/-! ## Absolute degrees: total-function placement

Everything downstream lives in absolute degrees `j : ℕ`, as total
functions vanishing outside the relevant window — the analogue of `Amat`'s
totality on ℤ², which rung B found load-bearing. -/

/-- Extension of an `f`-vector by zero to a total function on ℕ. -/
def extN {n : ℕ} (s : Fin (n + 1) → ℕ) : ℕ → ℕ :=
  fun m => if h : m ≤ n then s ⟨m, Nat.lt_succ_of_le h⟩ else 0

@[simp] theorem extN_val {n : ℕ} (s : Fin (n + 1) → ℕ) (m : Fin (n + 1)) :
    extN s m.val = s m := by
  simp only [extN]
  split_ifs with h
  · exact congrArg s (Fin.eta m _)
  · exact absurd m.is_le h

theorem extN_of_le {n : ℕ} {s : Fin (n + 1) → ℕ} {m : ℕ} (h : m ≤ n) :
    extN s m = s ⟨m, Nat.lt_succ_of_le h⟩ := by
  simp only [extN]
  split_ifs
  rfl

theorem extN_of_gt {n : ℕ} {s : Fin (n + 1) → ℕ} {m : ℕ} (h : n < m) :
    extN s m = 0 := by
  simp only [extN]
  split_ifs with h'
  · exact absurd h' (by omega)
  · rfl

/-- Placement in absolute degrees: shift by `dk`, zero below `dk`. -/
def shiftAbs (dk : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  fun j => if dk ≤ j then f (j - dk) else 0

theorem shiftAbs_of_le {dk : ℕ} (f : ℕ → ℕ) {j : ℕ} (h : dk ≤ j) :
    shiftAbs dk f j = f (j - dk) := by
  simp only [shiftAbs]
  split_ifs
  rfl

theorem shiftAbs_of_lt {dk : ℕ} (f : ℕ → ℕ) {j : ℕ} (h : j < dk) :
    shiftAbs dk f j = 0 := by
  simp only [shiftAbs]
  split_ifs with h'
  · exact absurd h' (by omega)
  · rfl

@[simp] theorem shiftAbs_apply_add (dk : ℕ) (f : ℕ → ℕ) (m : ℕ) :
    shiftAbs dk f (m + dk) = f m := by
  rw [shiftAbs_of_le f (Nat.le_add_left dk m), Nat.add_sub_cancel]

/-- The note's `C_k(j) = C(n, j − d_k)`, zero below `d_k` — and zero above
`d_k + n` for free, since `C(n,m) = 0` for `m > n`. -/
def Cabs (n dk : ℕ) : ℕ → ℕ :=
  shiftAbs dk fun m => n.choose m

/-- Below its window a component contributes the full binomial: at
absolute degree `j < indeg(s⃗) + dk`, the placed entry is `C_k(j)`.
(The single-component half of Lemma 2(b), from Lemma 1.) -/
theorem shiftAbs_extN_of_lt_indeg {n : ℕ} {s : Fin (n + 1) → ℕ}
    (hs : s ∈ Fn n) {dk j : ℕ} (h : (j : ℤ) < (indeg s : ℤ) + dk) :
    shiftAbs dk (extN s) j = Cabs n dk j := by
  rcases lt_or_ge j dk with hj | hj
  · rw [shiftAbs_of_lt _ hj, Cabs, shiftAbs_of_lt _ hj]
  · have h1 : j - dk < indeg s := by omega
    have h2 : j - dk ≤ n := by have := indeg_le s; omega
    rw [Cabs, shiftAbs_of_le _ hj, shiftAbs_of_le _ hj, extN_of_le h2]
    exact apply_eq_choose_of_lt_indeg hs h1

/-- Above its window a component contributes zero: at absolute degree
`j > tp(s⃗) + dk`, the placed entry vanishes.  (No membership in `𝓕_n`
needed — `Stats.lean`'s `apply_eq_zero_of_top_lt` is unconditional.) -/
theorem shiftAbs_extN_of_top_lt {n : ℕ} {s : Fin (n + 1) → ℕ} {dk j : ℕ}
    (h : top s + dk < (j : ℤ)) : shiftAbs dk (extN s) j = 0 := by
  rcases lt_or_ge j dk with hj | hj
  · exact shiftAbs_of_lt _ hj
  · rw [shiftAbs_of_le _ hj]
    rcases lt_or_ge n (j - dk) with h2 | h2
    · exact extN_of_gt h2
    · rw [extN_of_le h2]
      exact apply_eq_zero_of_top_lt
        (show top s < ((j - dk : ℕ) : ℤ) by omega)

/-- The componentwise cap: a placed entry never exceeds the binomial. -/
theorem shiftAbs_extN_le_Cabs {n : ℕ} {s : Fin (n + 1) → ℕ}
    (hs : s ∈ Fn n) (dk j : ℕ) : shiftAbs dk (extN s) j ≤ Cabs n dk j := by
  rcases lt_or_ge j dk with hj | hj
  · rw [shiftAbs_of_lt _ hj, Cabs, shiftAbs_of_lt _ hj]
  · rw [Cabs, shiftAbs_of_le _ hj, shiftAbs_of_le _ hj]
    rcases lt_or_ge n (j - dk) with h2 | h2
    · rw [extN_of_gt h2]
      exact Nat.zero_le _
    · rw [extN_of_le h2]
      exact apply_le_choose_of_mem_Fn hs _

/-! ## The sum map, the clamp and the chaining condition -/

/-- The sum map `Φ` of the note's §0, in absolute degrees:
`Φ(s⃗_1,…,s⃗_r)(j) = Σ_k s_k(j − d_k)`, each summand read as zero outside
its window. -/
def Phi {n r : ℕ} (d : Fin r → ℕ) (s : Fin r → Fin (n + 1) → ℕ) : ℕ → ℕ :=
  fun j => ∑ k, shiftAbs (d k) (extN (s k)) j

/-- The note's `y_c`: the partial sum of the components `k < c`
(0-based). -/
def headPhi {n r : ℕ} (d : Fin r → ℕ) (s : Fin r → Fin (n + 1) → ℕ)
    (c : ℕ) : ℕ → ℕ :=
  fun j => ∑ k ∈ univ.filter fun k : Fin r => k.val < c,
    shiftAbs (d k) (extN (s k)) j

/-- The tail binomial sum `Σ_{k ≥ c} C_k(j)` (0-based; the note's
`Σ_{k > i} C_k(j)` at 1-based `i = c`). -/
def tailC {r : ℕ} (n : ℕ) (d : Fin r → ℕ) (c : ℕ) : ℕ → ℕ :=
  fun j => ∑ k ∈ univ.filter fun k : Fin r => c ≤ k.val, Cabs n (d k) j

/-- The water-filling clamp `Q_c(j) = max(0, x(j) − Σ_{k≥c} C_k(j))` of
`eq:water-filling` — the outer `max(0,·)` **is** ℕ-truncated
subtraction. -/
def Qclamp {r : ℕ} (n : ℕ) (d : Fin r → ℕ) (c : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun j => x j - tailC n d c j

/-- The greedy slice `ŝ_i(m) = Q_{i+1}(m + d_i) − Q_i(m + d_i)` (0-based
`i`; the note's `ŝ_i(m) = Q_i(m+d_i) − Q_{i−1}(m+d_i)`, 1-based). -/
def greedySlice {r : ℕ} (n : ℕ) (d : Fin r → ℕ) (x : ℕ → ℕ) (i : Fin r) :
    Fin (n + 1) → ℕ :=
  fun m => Qclamp n d (i.val + 1) x (m.val + d i) -
    Qclamp n d i.val x (m.val + d i)

/-- `t̂_i = tp(s⃗_i) + d_i`, the absolute top degree of component `i`. -/
def hatTop {n r : ℕ} (d : Fin r → ℕ) (s : Fin r → Fin (n + 1) → ℕ)
    (i : Fin r) : ℤ :=
  top (s i) + d i

/-- `ρ̂_i = indeg(s⃗_i) + d_i`, the absolute initial degree of component
`i` (ℤ-valued, for uniform comparison with `hatTop`). -/
def hatIndeg {n r : ℕ} (d : Fin r → ℕ) (s : Fin r → Fin (n + 1) → ℕ)
    (i : Fin r) : ℤ :=
  (indeg (s i) : ℤ) + d i

/-- The chaining condition of `thm-chaining`, in the absolute form of the
note's §0: `t̂_i < ρ̂_{i+1}` for adjacent components.  Equivalent to the
manuscript's printed `tp(s⃗_{i-1}) < indeg(s⃗_i) + δ_i` when `d` is sorted
(`chained_iff_gap`), but stated without the gap vector `δ`. -/
def Chained {n r : ℕ} (d : Fin r → ℕ) (s : Fin r → Fin (n + 1) → ℕ) :
    Prop :=
  ∀ ⦃i j : Fin r⦄, i.val + 1 = j.val → hatTop d s i < hatIndeg d s j

/-- **The dictionary to the manuscript's printed form** (`thm-chaining`):
under `Monotone d` (the manuscript's sortedness hypothesis), the absolute
chaining condition is equivalent to the printed
`tp(s⃗_{i-1}) < indeg(s⃗_i) + δ_i`, `δ_i = d_i − d_{i-1} ∈ ℕ`.
Monotonicity is used **only in the ⟸ direction**: the absolute form
implies the printed one for arbitrary `d`, truncation or no truncation. -/
theorem chained_iff_gap {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hd : Monotone d) :
    Chained d s ↔ ∀ ⦃i j : Fin r⦄, i.val + 1 = j.val →
      top (s i) < (indeg (s j) : ℤ) + ((d j - d i : ℕ) : ℤ) := by
  constructor
  · intro h i j hij
    have h1 := h hij
    simp only [hatTop, hatIndeg] at h1
    omega
  · intro h i j hij
    have h1 := h hij
    have hle : d i ≤ d j := hd (Fin.le_def.mpr (by omega))
    simp only [hatTop, hatIndeg]
    omega

/-! ## Lemma 2(a): windows normal form -/

/-- `ρ̂_i ≤ t̂_i + 1` always: `Stats.lean`'s support condition
`indeg ≤ tp + 1`, shifted into absolute degrees. -/
theorem hatIndeg_le_hatTop_add_one {n r : ℕ} (d : Fin r → ℕ)
    (s : Fin r → Fin (n + 1) → ℕ) (i : Fin r) :
    hatIndeg d s i ≤ hatTop d s i + 1 := by
  have := indeg_le_top_add_one (s i)
  simp only [hatTop, hatIndeg]
  omega

/-- Lemma 2(a): the absolute tops of a chained tuple are monotone.  (No
`𝓕_n` membership and no sortedness of `d` are needed: chaining alone
forces the windows into position.) -/
theorem hatTop_mono {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hc : Chained d s) :
    Monotone (hatTop d s) := by
  intro i j hij
  suffices H : ∀ m : ℕ, ∀ j : Fin r, j.val = i.val + m →
      hatTop d s i ≤ hatTop d s j by
    exact H (j.val - i.val) j (by have := Fin.le_def.mp hij; omega)
  intro m
  induction m with
  | zero =>
    intro j hj
    have hij' : i = j := Fin.ext (by omega)
    exact hij' ▸ le_refl _
  | succ m ih =>
    intro j hj
    have hlt : i.val + m < r := by have := j.isLt; omega
    have h1 := ih ⟨i.val + m, hlt⟩ rfl
    have h2 : hatTop d s ⟨i.val + m, hlt⟩ < hatIndeg d s j :=
      hc (show i.val + m + 1 = j.val by omega)
    have h3 := hatIndeg_le_hatTop_add_one d s j
    omega

/-- Lemma 2(a): the free windows of a chained tuple are pairwise disjoint
and in order — `t̂_i < ρ̂_j` for **every** `i < j`, not only adjacent
pairs. -/
theorem hatTop_lt_hatIndeg {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hc : Chained d s) {i j : Fin r}
    (hij : i < j) : hatTop d s i < hatIndeg d s j := by
  have h0 : i.val < j.val := hij
  have hlt : j.val - 1 < r := by have := j.isLt; omega
  have h1 : hatTop d s i ≤ hatTop d s ⟨j.val - 1, hlt⟩ :=
    hatTop_mono hc (Fin.le_def.mpr (show i.val ≤ j.val - 1 by omega))
  have h2 : hatTop d s ⟨j.val - 1, hlt⟩ < hatIndeg d s j :=
    hc (show j.val - 1 + 1 = j.val by omega)
  omega

/-- Lemma 2(a): the absolute initial degrees of a chained tuple are
monotone. -/
theorem hatIndeg_mono {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hc : Chained d s) :
    Monotone (hatIndeg d s) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have h1 := hatTop_lt_hatIndeg hc hlt
    have h2 := hatIndeg_le_hatTop_add_one d s i
    omega

/-- Lemma 2(b), uniqueness clause: at most one component is free in any
given absolute degree — two components whose free windows share a degree
coincide. -/
theorem window_disjoint {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hc : Chained d s) {i k : Fin r} {j : ℕ}
    (hi1 : hatIndeg d s i ≤ (j : ℤ)) (hi2 : (j : ℤ) ≤ hatTop d s i)
    (hk1 : hatIndeg d s k ≤ (j : ℤ)) (hk2 : (j : ℤ) ≤ hatTop d s k) :
    i = k := by
  rcases lt_trichotomy i k with h | h | h
  · have := hatTop_lt_hatIndeg hc h
    exfalso; omega
  · exact h
  · have := hatTop_lt_hatIndeg hc h
    exfalso; omega

/-- The case split of Theorem A's proof: for every cut `c` and absolute
degree `j`, either every component from `c` on is at or below the start of
its window (`j < ρ̂_k`), or every component before `c` is past its window
(`t̂_k < j`).  Lemma 2(a) guarantees at least one alternative. -/
theorem chained_dichotomy {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hc : Chained d s) (c j : ℕ) :
    (∀ k : Fin r, c ≤ k.val → (j : ℤ) < hatIndeg d s k) ∨
      (∀ k : Fin r, k.val < c → hatTop d s k < (j : ℤ)) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact Or.inr fun k hk => absurd hk (Nat.not_lt_zero _)
  rcases lt_or_ge (c - 1) r with hcr | hcr
  · rcases lt_or_ge (hatTop d s ⟨c - 1, hcr⟩) (j : ℤ) with hj | hj
    · refine Or.inr fun k hk => lt_of_le_of_lt (hatTop_mono hc ?_) hj
      exact Fin.le_def.mpr (show k.val ≤ c - 1 by omega)
    · refine Or.inl fun k hk => ?_
      have h1 : (⟨c - 1, hcr⟩ : Fin r) < k := show c - 1 < k.val by omega
      have h2 := hatTop_lt_hatIndeg hc h1
      omega
  · exact Or.inl fun k hk => absurd k.isLt (by omega)

/-! ## Lemma 2(b) and Theorem A -/

/-- Splitting the sum map at a cut `c`: head components plus tail
components. -/
theorem phi_split {n r : ℕ} (d : Fin r → ℕ) (s : Fin r → Fin (n + 1) → ℕ)
    (c j : ℕ) :
    Phi d s j = headPhi d s c j +
      ∑ k ∈ univ.filter fun k : Fin r => c ≤ k.val,
        shiftAbs (d k) (extN (s k)) j := by
  simp only [Phi, headPhi]
  have hfil : (univ.filter fun k : Fin r => c ≤ k.val) =
      univ.filter fun k : Fin r => ¬k.val < c :=
    filter_congr fun k _ => not_lt.symm
  rw [hfil]
  exact (sum_filter_add_sum_filter_not univ _ _).symm

/-- Peeling the top component off a head sum. -/
theorem headPhi_succ {n r : ℕ} (d : Fin r → ℕ)
    (s : Fin r → Fin (n + 1) → ℕ) (i : Fin r) (j : ℕ) :
    headPhi d s (i.val + 1) j =
      headPhi d s i.val j + shiftAbs (d i) (extN (s i)) j := by
  simp only [headPhi]
  have hins : (univ.filter fun k : Fin r => k.val < i.val + 1) =
      insert i (univ.filter fun k : Fin r => k.val < i.val) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hk)
      · omega
      · omega
  rw [hins, sum_insert (by simp)]
  exact Nat.add_comm _ _

/-- Lemma 2(b), gap case: in an absolute degree past window `c − 1` and
short of window `c` (0-based; out-of-range window conditions are vacuous,
and `c ≤ r`), the sum is exactly the tail binomial sum. -/
theorem phi_eq_tailC {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hF : ∀ i, s i ∈ Fn n)
    (hc : Chained d s) {c j : ℕ} (hcr : c ≤ r)
    (h1 : ∀ i : Fin r, i.val + 1 = c → hatTop d s i < (j : ℤ))
    (h2 : ∀ i : Fin r, i.val = c → (j : ℤ) < hatIndeg d s i) :
    Phi d s j = tailC n d c j := by
  rw [phi_split d s c j]
  have hhead : headPhi d s c j = 0 := by
    simp only [headPhi]
    refine sum_eq_zero fun k hk => ?_
    have hk' := (mem_filter.mp hk).2
    have hcr' : c - 1 < r := by omega
    have hstep := h1 ⟨c - 1, hcr'⟩ (show c - 1 + 1 = c by omega)
    have hmono : hatTop d s k ≤ hatTop d s ⟨c - 1, hcr'⟩ :=
      hatTop_mono hc (Fin.le_def.mpr (show k.val ≤ c - 1 by omega))
    refine shiftAbs_extN_of_top_lt ?_
    simp only [hatTop] at hstep hmono
    omega
  have htail : ∑ k ∈ univ.filter fun k : Fin r => c ≤ k.val,
      shiftAbs (d k) (extN (s k)) j = tailC n d c j := by
    simp only [tailC]
    refine sum_congr rfl fun k hk => ?_
    have hk' := (mem_filter.mp hk).2
    have hcr'' : c < r := by have := k.isLt; omega
    have hstep := h2 ⟨c, hcr''⟩ rfl
    have hmono : hatIndeg d s ⟨c, hcr''⟩ ≤ hatIndeg d s k :=
      hatIndeg_mono hc (Fin.le_def.mpr (show c ≤ k.val by omega))
    refine shiftAbs_extN_of_lt_indeg (hF k) ?_
    simp only [hatIndeg] at hstep hmono
    omega
  rw [hhead, htail, Nat.zero_add]

/-- Lemma 2(b), window case: in an absolute degree inside component `i`'s
free window, the sum is the tail binomial sum past `i` plus component
`i`'s own entry, which is strictly between `0` and the binomial. -/
theorem phi_eq_add_of_mem_window {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hF : ∀ i, s i ∈ Fn n)
    (hc : Chained d s) {i : Fin r} {j : ℕ}
    (h1 : hatIndeg d s i ≤ (j : ℤ)) (h2 : (j : ℤ) ≤ hatTop d s i) :
    Phi d s j = tailC n d (i.val + 1) j + shiftAbs (d i) (extN (s i)) j ∧
      0 < shiftAbs (d i) (extN (s i)) j ∧
      shiftAbs (d i) (extN (s i)) j < Cabs n (d i) j := by
  have h1' : (indeg (s i) : ℤ) + d i ≤ (j : ℤ) := by
    simpa only [hatIndeg] using h1
  have h2' : (j : ℤ) ≤ top (s i) + d i := by
    simpa only [hatTop] using h2
  have hd1 : d i ≤ j := by omega
  have hd2 : j - d i ≤ n := by have := top_le (s i); omega
  have happ : shiftAbs (d i) (extN (s i)) j =
      s i ⟨j - d i, Nat.lt_succ_of_le hd2⟩ := by
    rw [shiftAbs_of_le _ hd1, extN_of_le hd2]
  refine ⟨?_, ?_, ?_⟩
  · rw [phi_split d s (i.val + 1) j, headPhi_succ]
    have hhead : headPhi d s i.val j = 0 := by
      simp only [headPhi]
      refine sum_eq_zero fun k hk => ?_
      have hk' := (mem_filter.mp hk).2
      have hlt : hatTop d s k < hatIndeg d s i :=
        hatTop_lt_hatIndeg hc (show k.val < i.val from hk')
      refine shiftAbs_extN_of_top_lt ?_
      simp only [hatTop, hatIndeg] at hlt
      omega
    have htail : ∑ k ∈ univ.filter fun k : Fin r => i.val + 1 ≤ k.val,
        shiftAbs (d k) (extN (s k)) j = tailC n d (i.val + 1) j := by
      simp only [tailC]
      refine sum_congr rfl fun k hk => ?_
      have hk' := (mem_filter.mp hk).2
      have hlt : hatTop d s i < hatIndeg d s k :=
        hatTop_lt_hatIndeg hc (show i.val < k.val by omega)
      refine shiftAbs_extN_of_lt_indeg (hF k) ?_
      simp only [hatTop, hatIndeg] at hlt
      omega
    rw [hhead, htail, Nat.zero_add, Nat.add_comm]
  · rw [happ]
    exact apply_pos_of_le_top (hF i)
      (show (((j - d i : ℕ)) : ℤ) ≤ top (s i) by omega)
  · rw [happ, Cabs, shiftAbs_of_le _ hd1]
    exact apply_lt_choose_of_indeg_le (hF i)
      (show indeg (s i) ≤ j - d i by omega)

/-- **The heart of Theorem A**: on the sum of a chained tuple, the clamp
`Q_c` recovers the partial sum `y_c` exactly, in every absolute degree.
ℕ-truncated subtraction absorbs the note's `max(0,·)`: in the alternative
`j < ρ̂_{c+1}` the subtraction is exact, in the alternative `j > t̂_c` it
truncates to zero, which is the correct value. -/
theorem Qclamp_phi {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hF : ∀ i, s i ∈ Fn n)
    (hc : Chained d s) (c j : ℕ) :
    Qclamp n d c (Phi d s) j = headPhi d s c j := by
  have hsplit := phi_split d s c j
  simp only [Qclamp]
  rcases chained_dichotomy hc c j with hA | hB
  · -- every component from `c` on is full: the subtraction is exact
    have htail : ∑ k ∈ univ.filter fun k : Fin r => c ≤ k.val,
        shiftAbs (d k) (extN (s k)) j = tailC n d c j := by
      simp only [tailC]
      refine sum_congr rfl fun k hk => ?_
      have hk' := (mem_filter.mp hk).2
      refine shiftAbs_extN_of_lt_indeg (hF k) ?_
      have := hA k hk'
      simp only [hatIndeg] at this
      omega
    rw [hsplit, htail]
    exact Nat.add_sub_cancel _ _
  · -- every component before `c` is spent: both sides vanish
    have hhead : headPhi d s c j = 0 := by
      simp only [headPhi]
      refine sum_eq_zero fun k hk => ?_
      have hk' := (mem_filter.mp hk).2
      refine shiftAbs_extN_of_top_lt ?_
      have := hB k hk'
      simp only [hatTop] at this
      omega
    have hle : Phi d s j ≤ tailC n d c j := by
      rw [hsplit, hhead, Nat.zero_add]
      simp only [tailC]
      exact sum_le_sum fun k _ => shiftAbs_extN_le_Cabs (hF k) (d k) j
    omega

/-- **Theorem A** (`eq:water-filling` inverts `Φ`): the greedy slices of
the sum of a chained tuple are the tuple itself — the closed-form
degreewise clamp reconstructs every chained tuple from its sum. -/
theorem greedySlice_phi {n r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} (hF : ∀ i, s i ∈ Fn n)
    (hc : Chained d s) (i : Fin r) :
    greedySlice n d (Phi d s) i = s i := by
  funext m
  simp only [greedySlice]
  rw [Qclamp_phi hF hc, Qclamp_phi hF hc, headPhi_succ,
    Nat.add_sub_cancel_left, shiftAbs_apply_add]
  exact extN_val (s i) m

/-- **Corollary of Theorem A**: `Φ` is injective on chained tuples — the
clamp is an explicit left inverse, so two chained tuples with the same sum
coincide.  This is the injectivity half of `thm-chaining`'s bijection. -/
theorem eq_of_phi_eq_phi {n r : ℕ} {d : Fin r → ℕ}
    {s s' : Fin r → Fin (n + 1) → ℕ}
    (hF : ∀ i, s i ∈ Fn n) (hF' : ∀ i, s' i ∈ Fn n)
    (hc : Chained d s) (hc' : Chained d s') (h : Phi d s = Phi d s') :
    s = s' := by
  funext i
  rw [← greedySlice_phi hF hc i, ← greedySlice_phi hF' hc' i, h]

/-- The same, packaged as `Set.InjOn` on the chained locus. -/
theorem phi_injOn_chained (n r : ℕ) (d : Fin r → ℕ) :
    Set.InjOn (Phi d)
      {s : Fin r → Fin (n + 1) → ℕ | (∀ i, s i ∈ Fn n) ∧ Chained d s} :=
  fun _ hs _ hs' h => eq_of_phi_eq_phi hs.1 hs'.1 hs.2 hs'.2 h

/-! ## The bridge to article 1's ℝ-valued `ffvec` -/

/-- On the `f`-vector of a family, the ℕ-extension is `fEntry` itself,
totally: `fEntry` already vanishes above `n`. -/
theorem extN_fvecN {n : ℕ} (D : Finset (Finset (Fin n))) :
    extN (fvecN D) = fun m => fEntry D m := by
  funext m
  simp only [extN]
  split_ifs with h
  · rfl
  · exact (fEntry_eq_zero_of_lt (by omega)).symm

/-- `Φ` is the ℕ-valued shadow of `Spine/Sumset.lean`'s ℝ-valued `ffvec`:
article 2's sum map and article 1's `ff`-vector agree entrywise, so the
injectivity above is a statement about the same objects `prop-sumset`
sums. -/
theorem ffvec_eq_phi {n r N : ℕ} (d : Fin r → ℕ)
    (D : Fin r → Finset (Finset (Fin n))) (j : Fin (N + 1)) :
    ffvec N d D j = ((Phi d fun k => fvecN (D k)) j.val : ℝ) := by
  simp only [ffvec, Phi]
  rw [Nat.cast_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [extN_fvecN]
  simp only [shiftAbs]
  split_ifs with h
  · rfl
  · exact Nat.cast_zero.symm

end ExteriorConvex
