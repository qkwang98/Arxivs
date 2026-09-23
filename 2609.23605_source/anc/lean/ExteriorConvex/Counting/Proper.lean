/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D3a of the article-2 formalisation: the proper statistics and counting layer

Formalisation of the counting content of `thm-proper` from
`article/exterior-convex_article2_draft_3.org`, per
`working-notes/PLAN-formalise-article2.org` (rung D3a).

Contents, by manuscript item:

* **The bridge** (`SnF_eq_filter_indeg`), and it is load-bearing: for
  `n ≥ 1`, `S_n = {s⃗ ∈ 𝓕_n : indeg(s⃗) ≥ 2}` — rung B's `SnF` (defined
  through `IsComplex` families) is exactly the `indeg ≥ 2` locus of
  `𝓕_n`.  This is the first sentence of `thm-proper`'s proof and the
  reason zeroing columns `ρ = 0, 1` implements properness; rung B's
  results speak of `SnF`, everything downstream here wants the `indeg`
  form.  **A finding of the formalisation: `n ≥ 1` is genuinely
  needed.**  At `n = 0` the sole member of `S_0` is the full vector
  `(1)`, whose `indeg` is `n + 1 = 1 < 2`, so the filter is empty while
  `S_0` is not — and consequently every `SnF`-facing statement below
  carries `1 ≤ n`, while the `indeg`-form statements are unconditional.
  (The manuscript's standing `n ≥ 1` covers this; the boundary is worth
  recording because `A′ = 0` at `n = 0`, so `thm-proper`'s identity
  would genuinely fail there, `1 ≠ 0`.)
* **`A′`, `u⃗′`, `T′(δ)`** (`thm-proper`): `Apmat` is `Amat` with columns
  `ρ = 0` and `ρ = 1` zeroed — a one-line modification, not a new
  object.  `upVec` is its row sums and `Tpmat` is built from `Apmat`
  exactly as `def-uT` builds `T` from `A`, reusing `Transfer.lean`'s
  conventions (`Fin (n+2)` indexing via `tauOf`, total in `δ : ℤ`, `ρ`
  summed over `Finset.Icc 0 (n+1)`).  The entry-as-a-count dictionaries
  are `upVec_eq_card`/`Tpmat_apply_eq_card` (`indeg` form,
  unconditional) and `upVec_eq_card_SnF`/`Tpmat_apply_eq_card_SnF`
  (`S_n` form, `n ≥ 1`).
* **`thm-proper`, counting identity**, in the same two-layer split as
  rung C2 and for the same reason:
  - **unconditional** (`card_properChainedTuples`): the number of proper
    chained tuples is `u⃗′ T′(δ₂)⋯T′(δ_r) 1⃗`, no hypothesis at all,
    gaps as honest ℤ-differences (`card_properChainedTuples_of_monotone`
    for the printed ℕ-gaps, `card_SnF_chainedTuples` for the printed
    `S_n^r` form of `eq:auto-16`);
  - **conditional** (`card_ffSetPrN`): the `|FF_pr(d⃗)|` form, with an
    explicit `Set.SurjOn` hypothesis.  **That hypothesis covers two
    things**: the surjectivity half of `thm-chaining` (open
    combinatorially; its algebraic proof is rung C3, a non-target) *and*
    `lem-lexproper` (that the lex representative of a properly
    achievable Hilbert function is itself proper — Amata–Crupi
    lex-submodule algebra, out of scope for the same reason as C3).
    Injectivity costs nothing: proper chained tuples are chained tuples,
    so rung C1's `phi_injOn_chained` restricts (`Set.InjOn.mono`).

The invariant-block repair of the proper `δ = 0` theory (rung D3b) is in
`Counting/ProperBlock.lean`; `prop-proper-threshold`/`λ_pr` (D3c) and the
proper exact degree (D3d) are deliberately not attempted here.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`); the sanity anchors — `|S_3| = 5`, the proper counts
`12`/`22` at `n = 3`, `r = 2`, `δ = 0`/`1` (`rem-proper-sequences`), the
proper counts `45`/`51` at `d⃗ = (0,0,1)`/`(0,1,1)` against the improper
`236`/`236` (`eq:proper-not-reversible`), and `|FF_pr(2;0^r)| = r + 1` —
were `#eval`s during development (recorded in
`runs/proper-lean-anchors-20260918.md`) and stay out of the formal
statements, deliberately.
-/
import ExteriorConvex.Counting.Transfer
import ExteriorConvex.Counting.Duality

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## The bridge: `S_n` is the `indeg ≥ 2` locus of `𝓕_n` -/

/-- **The bridge lemma of rung D3** (`thm-proper`'s proof, first
sentence): for `n ≥ 1`, `S_n = {s⃗ ∈ 𝓕_n : indeg(s⃗) ≥ 2}`.  Rung B's
`SnF` is defined through `IsComplex`; this is its `indeg` form, which is
what the column-zeroing of `A′` implements.  `n ≥ 1` is genuinely
needed: at `n = 0` the full vector has `indeg = 1`, so the right-hand
side is empty while `S_0 = {(1)}` is not. -/
theorem SnF_eq_filter_indeg (hn : 1 ≤ n) :
    SnF n = (Fn n).filter fun s => 2 ≤ indeg s := by
  ext s
  rw [mem_SnF_iff hn, Finset.mem_filter]
  constructor
  · rintro ⟨hsF, h0, h1⟩
    refine ⟨hsF, ?_⟩
    rw [le_indeg_iff (by omega)]
    intro j hj
    rcases (by omega : j.val = 0 ∨ j.val = 1) with h | h
    · have hj0 : j = (⟨0, by omega⟩ : Fin (n + 1)) := Fin.ext h
      rw [hj0, h0]
      simp
    · have hj1 : j = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext h
      rw [hj1, h1, Nat.choose_one_right]
  · rintro ⟨hsF, h2⟩
    have hle0 : s ⟨0, by omega⟩ ≤ n.choose 0 :=
      apply_le_choose_of_mem_Fn hsF ⟨0, by omega⟩
    have hge0 : n.choose 0 ≤ s ⟨0, by omega⟩ :=
      choose_le_of_lt_indeg (s := s) (j := ⟨0, by omega⟩)
        (show (0 : ℕ) < indeg s by omega)
    have hle1 : s ⟨1, by omega⟩ ≤ n.choose 1 :=
      apply_le_choose_of_mem_Fn hsF ⟨1, by omega⟩
    have hge1 : n.choose 1 ≤ s ⟨1, by omega⟩ :=
      choose_le_of_lt_indeg (s := s) (j := ⟨1, by omega⟩)
        (show (1 : ℕ) < indeg s by omega)
    rw [Nat.choose_zero_right] at hle0 hge0
    rw [Nat.choose_one_right] at hle1 hge1
    exact ⟨hsF, by omega, by omega⟩

/-! ## `A′`: the matrix `A` with columns `ρ = 0, 1` zeroed -/

/-- `thm-proper`'s `A′`: `A` with the columns `ρ = 0` and `ρ = 1` set to
zero — a one-line modification of `Amat`, not a new object.  Total in
`(τ, ρ) : ℤ × ℤ` like `Amat` itself. -/
def Apmat (n : ℕ) (τ ρ : ℤ) : ℕ :=
  if ρ < 2 then 0 else Amat n τ ρ

theorem Apmat_eq_zero_of_lt {τ ρ : ℤ} (h : ρ < 2) : Apmat n τ ρ = 0 := by
  rw [Apmat, ite_eq_left h]

theorem Apmat_eq_of_le {τ ρ : ℤ} (h : 2 ≤ ρ) : Apmat n τ ρ = Amat n τ ρ := by
  rw [Apmat, ite_eq_right (by omega)]

/-- `A′` inherits `A`'s support bound `ρ ≤ τ + 1`. -/
theorem Apmat_eq_zero_of_add_one_lt {τ ρ : ℤ} (h : τ + 1 < ρ) :
    Apmat n τ ρ = 0 := by
  rcases lt_or_ge ρ 2 with h2 | h2
  · exact Apmat_eq_zero_of_lt h2
  · rw [Apmat_eq_of_le h2]
    exact Amat_eq_zero_of_add_one_lt h

/-- **Rows `τ = −1` and `τ = 0` of `A′` vanish identically**: row `−1` of
`A` lives in column `ρ = 0` and row `0` of `A` lives in column `ρ = 1`
(the unique `s⃗` with `tp = 0` is `(1, 0, …, 0)`, of `indeg` `1`), and
both columns are zeroed in `A′`.  This is the support fact behind rung
D3b's invariant-block repair. -/
theorem Apmat_eq_zero_of_le_zero {τ ρ : ℤ} (h : τ ≤ 0) : Apmat n τ ρ = 0 := by
  rcases lt_or_ge ρ 2 with h2 | h2
  · exact Apmat_eq_zero_of_lt h2
  · rw [Apmat_eq_of_le h2]
    exact Amat_eq_zero_of_add_one_lt (by omega)

/-! ## The master counting dictionary for `A′`

The exact analogue of `sum_Amat_eq_card`: summing a row of `A′` over any
set `R` of `indeg`-values counts the members of `𝓕_n` in the
corresponding `tp`-class whose `indeg` is at least `2` *and* lies in
`R` — the column-zeroing is precisely the extra conjunct `2 ≤ indeg`. -/

theorem sum_Apmat_eq_card (n : ℕ) (τ : ℤ) (R : Finset ℤ) :
    ∑ ρ ∈ R, Apmat n τ ρ =
      #((Fn n).filter fun s =>
        top s = τ ∧ 2 ≤ indeg s ∧ (indeg s : ℤ) ∈ R) := by
  have hsplit : ∑ ρ ∈ R, Apmat n τ ρ =
      ∑ ρ ∈ R.filter (fun ρ => 2 ≤ ρ), Amat n τ ρ := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun ρ => 2 ≤ ρ)
      (Apmat n τ)]
    have h1 : ∑ ρ ∈ R.filter (fun ρ => ¬2 ≤ ρ), Apmat n τ ρ = 0 :=
      Finset.sum_eq_zero fun ρ hρ =>
        Apmat_eq_zero_of_lt
          (by have := (Finset.mem_filter.mp hρ).2; omega)
    rw [h1, add_zero]
    exact Finset.sum_congr rfl fun ρ hρ =>
      Apmat_eq_of_le (Finset.mem_filter.mp hρ).2
  rw [hsplit, sum_Amat_eq_card]
  congr 1
  ext s
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hsF, htop, hR, h2⟩
    exact ⟨hsF, htop, by omega, hR⟩
  · rintro ⟨hsF, htop, h2, hR⟩
    exact ⟨hsF, htop, hR, by omega⟩

/-! ## `u⃗′` and `T′(δ)` -/

/-- `thm-proper`'s `u⃗′`: the row sums of `A′`, over the supporting range
`ρ ∈ {0, …, n+1}` — exactly as `def-uT` builds `u⃗` from `A`. -/
def upVec (n : ℕ) : Fin (n + 2) → ℕ :=
  fun k => ∑ ρ ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), Apmat n (tauOf k) ρ

/-- The counting dictionary for `u⃗′`, `indeg` form (unconditional):
`u′[τ]` counts the `s⃗ ∈ 𝓕_n` with `tp(s⃗) = τ` and `indeg(s⃗) ≥ 2`. -/
theorem upVec_eq_card (n : ℕ) (k : Fin (n + 2)) :
    upVec n k =
      #((Fn n).filter fun s => top s = tauOf k ∧ 2 ≤ indeg s) := by
  simp only [upVec]
  rw [sum_Apmat_eq_card]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hsF, htop, h2, -⟩
    exact ⟨hsF, htop, h2⟩
  · rintro ⟨hsF, htop, h2⟩
    have := indeg_le s
    exact ⟨hsF, htop, h2, by omega, by omega⟩

/-- `thm-proper`'s `T′(δ)`, built from `A′` exactly as `def-uT` builds
`T(δ)` from `A` — same `Fin (n+2)` indexing, same row/column reading
(row `τ` the `tp` of the previous summand, column `τ'` the `tp` of the
current one), total in `δ : ℤ`. -/
def Tpmat (n : ℕ) (δ : ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℕ :=
  Matrix.of fun k k' =>
    ∑ ρ ∈ (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter
      (fun ρ => tauOf k - δ < ρ), Apmat n (tauOf k') ρ

theorem Tpmat_apply (n : ℕ) (δ : ℤ) (k k' : Fin (n + 2)) :
    Tpmat n δ k k' =
      ∑ ρ ∈ (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter
        (fun ρ => tauOf k - δ < ρ), Apmat n (tauOf k') ρ := rfl

/-- The counting dictionary for `T′(δ)`, `indeg` form (unconditional) —
the analogue of `Tmat_apply_eq_card`, through which every later claim
about `T′` is proved: `T′(δ)[τ][τ']` counts the `s⃗ ∈ 𝓕_n` with
`tp(s⃗) = τ'`, `indeg(s⃗) ≥ 2`, whose `indeg` clears the chaining bar
after a predecessor of `tp` equal to `τ`. -/
theorem Tpmat_apply_eq_card (n : ℕ) (δ : ℤ) (k k' : Fin (n + 2)) :
    Tpmat n δ k k' =
      #((Fn n).filter fun s => top s = tauOf k' ∧ 2 ≤ indeg s ∧
        tauOf k - δ < (indeg s : ℤ)) := by
  rw [Tpmat_apply, sum_Apmat_eq_card]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hsF, htop, h2, ⟨-, -⟩, hlt⟩
    exact ⟨hsF, htop, h2, hlt⟩
  · rintro ⟨hsF, htop, h2, hlt⟩
    have := indeg_le s
    exact ⟨hsF, htop, h2, ⟨by omega, by omega⟩, hlt⟩

/-! ### The `S_n` forms of the dictionaries (`n ≥ 1`, via the bridge) -/

/-- The `tp`-classes of `S_n` are the `indeg ≥ 2` classes of `𝓕_n`. -/
theorem filter_SnF_top (hn : 1 ≤ n) (τ : ℤ) :
    ((SnF n).filter fun s => top s = τ) =
      (Fn n).filter fun s => top s = τ ∧ 2 ≤ indeg s := by
  rw [SnF_eq_filter_indeg hn, Finset.filter_filter]
  exact Finset.filter_congr fun s _ => and_comm

/-- The counting dictionary for `u⃗′` over `S_n` (`thm-proper`'s
reading): `u′[τ]` counts the members of `S_n` with `tp = τ`. -/
theorem upVec_eq_card_SnF (hn : 1 ≤ n) (k : Fin (n + 2)) :
    upVec n k = #((SnF n).filter fun s => top s = tauOf k) := by
  rw [upVec_eq_card, filter_SnF_top hn]

/-- The counting dictionary for `T′(δ)` over `S_n`. -/
theorem Tpmat_apply_eq_card_SnF (hn : 1 ≤ n) (δ : ℤ) (k k' : Fin (n + 2)) :
    Tpmat n δ k k' =
      #((SnF n).filter fun s => top s = tauOf k' ∧
        tauOf k - δ < (indeg s : ℤ)) := by
  rw [Tpmat_apply_eq_card, SnF_eq_filter_indeg hn, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun s _ => ?_
  constructor
  · rintro ⟨htop, h2, hlt⟩
    exact ⟨h2, htop, hlt⟩
  · rintro ⟨h2, htop, hlt⟩
    exact ⟨htop, h2, hlt⟩

/-- `∑_τ u′[τ] = |{s⃗ ∈ 𝓕_n : indeg ≥ 2}|` — the row sums of `A′` total
the proper locus (the analogue of `sum_uVec`). -/
theorem sum_upVec (n : ℕ) :
    ∑ k : Fin (n + 2), upVec n k =
      #((Fn n).filter fun s => 2 ≤ indeg s) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s : Fin (n + 1) → ℕ => top s)
    (t := Finset.Icc (-1 : ℤ) (n : ℤ))
    (fun s _ => Finset.mem_Icc.mpr ⟨neg_one_le_top _, top_le _⟩),
    ← sum_tauOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [upVec_eq_card, Finset.filter_filter]
  exact congrArg Finset.card (Finset.filter_congr fun s _ => and_comm)

/-- `∑_τ u′[τ] = |S_n|` for `n ≥ 1`. -/
theorem sum_upVec_eq_card_SnF (hn : 1 ≤ n) :
    ∑ k : Fin (n + 2), upVec n k = #(SnF n) := by
  rw [sum_upVec, SnF_eq_filter_indeg hn]

/-! ## Proper chained tuples as a `Finset` -/

/-- The proper chained locus of `thm-proper`, in the `indeg` form:
chained tuples all of whose components have `indeg ≥ 2`.  For `n ≥ 1`
this is exactly the `S_n^r` chained locus of `eq:auto-16`
(`properChainedTuples_eq_filter_SnF`). -/
def properChainedTuples (n r : ℕ) (d : Fin r → ℕ) :
    Finset (Fin r → Fin (n + 1) → ℕ) :=
  (chainedTuples n r d).filter fun s => ∀ i, 2 ≤ indeg (s i)

theorem mem_properChainedTuples {r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} :
    s ∈ properChainedTuples n r d ↔
      (∀ i, s i ∈ Fn n) ∧ (∀ i, 2 ≤ indeg (s i)) ∧ Chained d s := by
  rw [properChainedTuples, Finset.mem_filter, mem_chainedTuples]
  tauto

/-- For `n ≥ 1` the proper chained locus is the `S_n`-tuple form of
`eq:auto-16`, via the bridge. -/
theorem properChainedTuples_eq_filter_SnF (hn : 1 ≤ n) (r : ℕ)
    (d : Fin r → ℕ) :
    properChainedTuples n r d =
      (Fintype.piFinset fun _ : Fin r => SnF n).filter (Chained d) := by
  ext s
  rw [mem_properChainedTuples, Finset.mem_filter, Fintype.mem_piFinset]
  have hbridge : ∀ i, s i ∈ SnF n ↔ s i ∈ Fn n ∧ 2 ≤ indeg (s i) :=
    fun i => by rw [SnF_eq_filter_indeg hn, Finset.mem_filter]
  constructor
  · rintro ⟨hF, h2, hch⟩
    exact ⟨fun i => (hbridge i).mpr ⟨hF i, h2 i⟩, hch⟩
  · rintro ⟨hS, hch⟩
    exact ⟨fun i => ((hbridge i).mp (hS i)).1,
      fun i => ((hbridge i).mp (hS i)).2, hch⟩

/-- The proper chained count refined by the `tp`-class of the last
component — the state vector of the proper transfer-matrix recursion.
`r` is the number of *gaps*; tuples have `r + 1` components. -/
def properChainedTopCount (n r : ℕ) (d : Fin (r + 1) → ℕ)
    (k : Fin (n + 2)) : ℕ :=
  #((properChainedTuples n (r + 1) d).filter fun s =>
    top (s (Fin.last r)) = tauOf k)

/-! ## The ordered product of proper transfer matrices

Like the `T(δ)`, the `T′(δ)` do not commute, so the product is the same
right-peeling recursion as `Tprod`, never a `Finset.prod`. -/

def Tpprod (n : ℕ) : (r : ℕ) → (Fin r → ℤ) →
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℕ
  | 0, _ => 1
  | r + 1, g => Tpprod n r (g ∘ Fin.castSucc) * Tpmat n (g (Fin.last r))

@[simp] theorem Tpprod_zero (n : ℕ) (g : Fin 0 → ℤ) : Tpprod n 0 g = 1 :=
  rfl

@[simp] theorem Tpprod_succ (n r : ℕ) (g : Fin (r + 1) → ℤ) :
    Tpprod n (r + 1) g =
      Tpprod n r (g ∘ Fin.castSucc) * Tpmat n (g (Fin.last r)) := rfl

/-! ## The base case and the inductive step -/

theorem properChainedTopCount_zero (n : ℕ) (d : Fin 1 → ℕ)
    (k : Fin (n + 2)) :
    properChainedTopCount n 0 d k =
      #((Fn n).filter fun s => top s = tauOf k ∧ 2 ≤ indeg s) := by
  simp only [properChainedTopCount]
  refine Finset.card_bij' (fun s _ => s (Fin.last 0)) (fun t _ => fun _ => t)
    ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    obtain ⟨hF, h2, -⟩ := mem_properChainedTuples.mp hs1
    exact Finset.mem_filter.mpr ⟨hF _, hs2, h2 _⟩
  · intro t ht
    obtain ⟨htF, htop, h2⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr
      ⟨mem_properChainedTuples.mpr ⟨fun _ => htF, fun _ => h2, ?_⟩, htop⟩
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  · intro s hs
    funext i
    have hi : i = Fin.last 0 := Fin.ext (by have := i.isLt; omega)
    rw [hi]
  · intro t ht
    rfl

/-- Componentwise properness over a `snoc` tuple (the analogue of
`snoc_mem_Fn_iff`). -/
theorem snoc_indeg_iff {r : ℕ} {s' : Fin (r + 1) → Fin (n + 1) → ℕ}
    {t : Fin (n + 1) → ℕ} :
    (∀ i, 2 ≤ indeg ((Fin.snoc s' t : Fin (r + 2) → Fin (n + 1) → ℕ) i)) ↔
      (∀ i, 2 ≤ indeg (s' i)) ∧ 2 ≤ indeg t := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The last-summand splitting for proper tuples — `card_chained_fiber`
with the properness of every component carried along; the second factor
is a `Tpmat` entry by `Tpmat_apply_eq_card`. -/
theorem card_properChained_fiber {r : ℕ} (d : Fin (r + 2) → ℕ)
    (τ' τ : ℤ) :
    #(((properChainedTuples n (r + 2) d).filter fun s =>
        top (s (Fin.last (r + 1))) = τ').filter fun s =>
        top (s ((Fin.last r).castSucc)) = τ) =
      #((properChainedTuples n (r + 1) (d ∘ Fin.castSucc)).filter fun s' =>
          top (s' (Fin.last r)) = τ) *
        #((Fn n).filter fun t => top t = τ' ∧ 2 ≤ indeg t ∧
            τ - ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc)) <
              (indeg t : ℤ)) := by
  rw [← Finset.card_product]
  refine Finset.card_bij'
    (fun s _ => (Fin.init s, s (Fin.last (r + 1))))
    (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_
  · -- forward: a proper chained tuple splits into a proper chained head
    -- and a valid proper tail
    intro s hs
    obtain ⟨hs1, hτ⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs2, hτ'⟩ := Finset.mem_filter.mp hs1
    obtain ⟨hpi, h2, hch⟩ := mem_properChainedTuples.mp hs2
    rw [← Fin.snoc_init_self s] at hch
    obtain ⟨hch', hlast⟩ := chained_snoc_iff.mp hch
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨mem_properChainedTuples.mpr
          ⟨fun i => hpi i.castSucc, fun i => h2 i.castSucc, hch'⟩, hτ⟩
    · refine Finset.mem_filter.mpr ⟨hpi _, hτ', h2 _, ?_⟩
      have hτeq : top (Fin.init s (Fin.last r)) = τ := hτ
      rw [hτeq] at hlast
      show τ - ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc)) <
        (indeg (s (Fin.last (r + 1))) : ℤ)
      omega
  · -- backward: `snoc` of a proper chained head and a valid proper tail
    rintro ⟨s', t⟩ hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    obtain ⟨hA1, hτ⟩ := Finset.mem_filter.mp hA
    obtain ⟨hpi', h2', hch'⟩ := mem_properChainedTuples.mp hA1
    obtain ⟨htF, hτ', h2t, hbar⟩ := Finset.mem_filter.mp hB
    have hbar' : τ - ((d (Fin.last (r + 1)) : ℤ) -
        d ((Fin.last r).castSucc)) < (indeg t : ℤ) := hbar
    have hch : Chained d (Fin.snoc s' t) := by
      refine chained_snoc_iff.mpr ⟨hch', ?_⟩
      rw [hτ]
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_properChainedTuples.mpr
        ⟨snoc_mem_Fn_iff.mpr ⟨hpi', htF⟩,
          snoc_indeg_iff.mpr ⟨h2', h2t⟩, hch⟩
    · rw [Fin.snoc_last]
      exact hτ'
    · rw [Fin.snoc_castSucc]
      exact hτ
  · intro s hs
    exact Fin.snoc_init_self s
  · rintro ⟨s', t⟩ hp
    simp only [Fin.init_snoc, Fin.snoc_last]

theorem properChainedTopCount_succ {r : ℕ} (d : Fin (r + 2) → ℕ)
    (k' : Fin (n + 2)) :
    properChainedTopCount n (r + 1) d k' =
      ∑ k : Fin (n + 2), properChainedTopCount n r (d ∘ Fin.castSucc) k *
        Tpmat n ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc))
          k k' := by
  simp only [properChainedTopCount]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s => top (s ((Fin.last r).castSucc)))
    (t := Finset.Icc (-1 : ℤ) (n : ℤ))
    (fun s _ => Finset.mem_Icc.mpr ⟨neg_one_le_top _, top_le _⟩),
    ← sum_tauOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [card_properChained_fiber d (tauOf k') (tauOf k), Tpmat_apply_eq_card]

/-! ## The main induction and the counting identity -/

theorem properChainedTopCount_eq (n r : ℕ) (d : Fin (r + 1) → ℕ) :
    properChainedTopCount n r d = upVec n ᵥ* Tpprod n r (gaps d) := by
  induction r with
  | zero =>
    funext k
    rw [Tpprod_zero, Matrix.vecMul_one]
    exact (properChainedTopCount_zero n d k).trans (upVec_eq_card n k).symm
  | succ r ih =>
    funext k'
    rw [properChainedTopCount_succ, Tpprod_succ, ← Matrix.vecMul_vecMul,
      ← gaps_comp_castSucc, ← ih (d ∘ Fin.castSucc), gaps_last]
    rfl

/-- **`thm-proper`, counting identity, unconditional** (the analogue of
C2a): the number of proper chained tuples is
`u⃗′ · T′(δ₂) ⋯ T′(δ_r) · 1⃗`, with the gaps as ℤ-differences.  No
hypothesis at all — not even `n ≥ 1`: in the `indeg` form both sides
count the same thing at every `n` (at `n = 0` both are `0`). -/
theorem card_properChainedTuples (n r : ℕ) (d : Fin (r + 1) → ℕ) :
    #(properChainedTuples n (r + 1) d) =
      upVec n ᵥ* Tpprod n r (gaps d) ⬝ᵥ onesCol n := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s => top (s (Fin.last r)))
    (t := Finset.Icc (-1 : ℤ) (n : ℤ))
    (fun s _ => Finset.mem_Icc.mpr ⟨neg_one_le_top _, top_le _⟩),
    ← sum_tauOf, dotProduct_onesCol]
  exact Finset.sum_congr rfl fun k _ =>
    congrFun (properChainedTopCount_eq n r d) k

/-- The counting identity in the manuscript's printed gap form: sorted
`d`, gaps as the ℕ-differences of `thm-proper`. -/
theorem card_properChainedTuples_of_monotone (n r : ℕ)
    {d : Fin (r + 1) → ℕ} (hd : Monotone d) :
    #(properChainedTuples n (r + 1) d) =
      upVec n ᵥ* Tpprod n r (fun i => ((d i.succ - d i.castSucc : ℕ) : ℤ)) ⬝ᵥ
        onesCol n := by
  rw [card_properChainedTuples, gaps_eq_of_monotone hd]

/-- **`thm-proper`, middle equality of `eq:auto-16`** (`n ≥ 1`): the
count of `S_n`-tuples satisfying the chaining condition is the proper
transfer product — the printed `#{(s⃗_1,…,s⃗_r) ∈ S_n^r : chained}` form,
via the bridge. -/
theorem card_SnF_chainedTuples (n r : ℕ) (hn : 1 ≤ n)
    (d : Fin (r + 1) → ℕ) :
    #((Fintype.piFinset fun _ : Fin (r + 1) => SnF n).filter (Chained d)) =
      upVec n ᵥ* Tpprod n r (gaps d) ⬝ᵥ onesCol n := by
  rw [← properChainedTuples_eq_filter_SnF hn, card_properChainedTuples]

/-! ## The conditional `|FF_pr(d⃗)|` form -/

/-- Article 2's `FF_pr(d⃗)`: the sums `∑ᵢ shift^{dᵢ}(s⃗ᵢ)` over all
tuples from `S_n` — the proper analogue of `ffSetN`, ℕ-valued in
absolute degrees per rung C1's total-function convention. -/
def ffSetPrN (n : ℕ) {r : ℕ} (d : Fin r → ℕ) : Set (ℕ → ℕ) :=
  {x | ∃ s : Fin r → Fin (n + 1) → ℕ, (∀ i, s i ∈ SnF n) ∧ Phi d s = x}

theorem coe_properChainedTuples (hn : 1 ≤ n) (r : ℕ) (d : Fin r → ℕ) :
    (properChainedTuples n r d : Set (Fin r → Fin (n + 1) → ℕ)) =
      {s | (∀ i, s i ∈ SnF n) ∧ Chained d s} := by
  ext s
  rw [Finset.mem_coe, properChainedTuples_eq_filter_SnF hn,
    Finset.mem_filter, Fintype.mem_piFinset]
  exact Iff.rfl

/-- **`thm-proper` as printed, modulo one explicit hypothesis.**
`hsurj` says every element of `FF_pr(d⃗)` is the sum of a *proper
chained* tuple.  **The hypothesis covers two open-for-Lean items at
once**: the surjectivity half of `thm-chaining` (open combinatorially;
its algebraic proof through Amata–Crupi lex theory is rung C3, a
non-target) *and* `lem-lexproper` (properness of the lex
representative — Amata–Crupi lex-submodule algebra of the same
category).  The manuscript proves `thm-proper` from exactly these two
inputs plus the rearrangement certified here.  Injectivity needs no
hypothesis: proper chained tuples are chained tuples, so rung C1's
`phi_injOn_chained` restricts. -/
theorem card_ffSetPrN (n r : ℕ) (hn : 1 ≤ n) (d : Fin (r + 1) → ℕ)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ SnF n) ∧ Chained d s}
      (ffSetPrN n d)) :
    (ffSetPrN n d).ncard =
      upVec n ᵥ* Tpprod n r (gaps d) ⬝ᵥ onesCol n := by
  have hsub : {s : Fin (r + 1) → Fin (n + 1) → ℕ |
      (∀ i, s i ∈ SnF n) ∧ Chained d s} ⊆
      {s | (∀ i, s i ∈ Fn n) ∧ Chained d s} := by
    rintro s ⟨hS, hch⟩
    exact ⟨fun i => SnF_subset_Fn (hS i), hch⟩
  have himg : ffSetPrN n d =
      Phi d '' {s | (∀ i, s i ∈ SnF n) ∧ Chained d s} := by
    refine Set.Subset.antisymm hsurj ?_
    rintro x ⟨s, ⟨hS, -⟩, rfl⟩
    exact ⟨s, hS, rfl⟩
  rw [himg,
    Set.InjOn.ncard_image ((phi_injOn_chained n (r + 1) d).mono hsub),
    ← coe_properChainedTuples hn, Set.ncard_coe_finset,
    card_properChainedTuples]

/-- `thm-proper` in the manuscript's literally printed form (sorted `d`,
ℕ-gaps), still modulo the combined surjectivity/`lem-lexproper`
hypothesis. -/
theorem card_ffSetPrN_of_monotone (n r : ℕ) (hn : 1 ≤ n)
    {d : Fin (r + 1) → ℕ} (hd : Monotone d)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ SnF n) ∧ Chained d s}
      (ffSetPrN n d)) :
    (ffSetPrN n d).ncard =
      upVec n ᵥ* Tpprod n r (fun i => ((d i.succ - d i.castSucc : ℕ) : ℤ)) ⬝ᵥ
        onesCol n := by
  rw [card_ffSetPrN n r hn d hsurj, gaps_eq_of_monotone hd]

end ExteriorConvex
