/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung C2 of the article-2 formalisation: the transfer-matrix count

Formalisation of `def-uT`, `thm-main` (as a counting statement) and
`cor-r1` from `article/exterior-convex_article2_draft_3.org`, per
`working-notes/PLAN-formalise-article2.org` (rung C2).

The rung is split so that the open part is visible in a type signature
rather than buried in a proof:

* **C2a (`card_chainedTuples`), unconditional**: the number of chained
  tuples over `𝓕_n` is the matrix product `u⃗ T(δ₂)⋯T(δ_r) 1⃗` of
  `eq:def-uT` — a pure `Finset` rearrangement, no hypothesis at all.
* **C2b (`card_ffSetN`), conditional**: `|FF(d⃗)|` equals the same
  product, **assuming as an explicit hypothesis** that `Φ` maps the
  chained locus onto `FF(d⃗)`.  That hypothesis is exactly the
  surjectivity half of `thm-chaining`, which is open combinatorially
  (its algebraic proof routes through Amata–Crupi lex theory) and is
  **deliberately not formalised** — rung C3 is a non-target, and the
  paper says "proved modulo" in the same place.  Injectivity is rung
  C1's `phi_injOn_chained` and carries no hypothesis.

Design decisions:

* **The matrices are indexed by `Fin (n+2)`**, with `tauOf k = k − 1`
  the dictionary to the manuscript's `τ, τ' ∈ {−1, 0, …, n}`
  (`eq:def-uT-range`).  This buys Mathlib's genuine `Matrix` product —
  the statement proved is the printed matrix identity, not an ad-hoc
  iterated sum — and rung D will need the `Matrix` API anyway.
* **`Tmat n δ` is total in `δ : ℤ`**, continuing the totalisation
  pattern of `Amat` (rung B) and `extN`/`shiftAbs` (rung C1): the
  printed definition restricts to `δ ≥ 0`, but the formula
  `∑_{ρ>τ−δ} A[τ'][ρ]` makes sense for every integer `δ`, and taking
  it totally is exactly what lets C2a hold for **arbitrary** `d`, with
  the gap `δᵢ = dᵢ − dᵢ₋₁` an honest ℤ-difference.  The printed form
  with ℕ-gaps is `card_chainedTuples_of_monotone`, where `Monotone d`
  is spent only on rewriting the gaps — the count itself never uses it,
  matching C1's finding that sortedness enters nowhere in the argument.
* **`ρ` is summed over `Finset.Icc 0 (n+1)`**, justified by the
  vanishing lemmas `Amat_eq_zero_of_neg`/`Amat_eq_zero_of_gt`;
  `uVec_eq_sum_row` states that any larger range gives the same row
  sum.
* **The induction peels the last summand**, via `Fin.snoc`/`Fin.init`,
  since the chained condition couples adjacent components only;
  `Tprod` is defined by matching right-peeling recursion so that the
  induction and the matrix product associate identically.

**The index order of `T(δ)` — the trap this rung must not fall into.**
By `rem-gap-reversal` the full product `u⃗ T(δ₂)⋯T(δ_r) 1⃗` is invariant
under reversing the gap vector, so *no numerical check can detect a
reversed product order*.  The order is fixed here by reading
`eq:def-uT`: in `T(δ)[τ][τ']`, **the row index `τ` is the `tp` of the
previous summand** (it enters only through the range condition
`ρ > τ − δ`), **the column index `τ'` is the `tp` of the current
summand** (it enters as the row of `A`), and `ρ` is the `indeg` of the
current summand, summed out.  `Tmat_apply_eq_card` states exactly this
reading as a count, and the C2a induction consumes it against the
`Chained` condition — `(v ᵥ* T) τ' = ∑_τ v τ · T τ τ'` matches "sum
over the previous top" only with this orientation, so a transposed
`Tmat` would make `chainedTopCount_succ` unprovable, not just untested.
Relatedly, the `T(δ)` do **not** commute (the manuscript exhibits
`T(1)T(2) ≠ T(2)T(1)`), so the product is a recursion/`Matrix` product
in a fixed order, never a `Finset.prod`.

**`native_decide` is banned in this development** (it would add the
axiom `Lean.ofReduceBool`); the sanity values `u⃗ = (1,1,3,4,1)`,
`u⃗T(0)1⃗ = 43` at `n = 3` were checked by `#eval` during development
and stay out of the formal statements, deliberately.
-/
import ExteriorConvex.Counting.Stats
import ExteriorConvex.Counting.Chaining

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## The index dictionary `Fin (n+2) ↔ {−1, 0, …, n}` -/

/-- The dictionary from the matrix index `k : Fin (n+2)` to the
manuscript's `τ ∈ {−1, 0, …, n}` (`eq:def-uT-range`): `tauOf k = k − 1`,
so `k = 0` is the void class `τ = −1` and `k = n+1` is the full-simplex
class `τ = n`. -/
def tauOf (k : Fin (n + 2)) : ℤ := (k.val : ℤ) - 1

theorem neg_one_le_tauOf (k : Fin (n + 2)) : -1 ≤ tauOf k := by
  simp only [tauOf]
  omega

theorem tauOf_le (k : Fin (n + 2)) : tauOf k ≤ (n : ℤ) := by
  have := k.isLt
  simp only [tauOf]
  omega

theorem tauOf_injective : Function.Injective (tauOf (n := n)) := by
  intro k k' h
  simp only [tauOf] at h
  exact Fin.ext (by omega)

/-- `{−1, 0, …, n}` is precisely the image of the index dictionary. -/
theorem Icc_eq_image_tauOf (n : ℕ) :
    Finset.Icc (-1 : ℤ) (n : ℤ) = Finset.image (tauOf (n := n)) univ := by
  ext τ
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(τ + 1).toNat, by omega⟩, ?_⟩
    show ((τ + 1).toNat : ℤ) - 1 = τ
    omega
  · rintro ⟨k, rfl⟩
    exact ⟨neg_one_le_tauOf k, tauOf_le k⟩

/-- Reindexing a sum over the manuscript's `τ`-range as a sum over
`Fin (n+2)`. -/
theorem sum_tauOf (n : ℕ) (g : ℤ → ℕ) :
    ∑ k : Fin (n + 2), g (tauOf k) = ∑ τ ∈ Finset.Icc (-1 : ℤ) (n : ℤ), g τ := by
  rw [Icc_eq_image_tauOf,
    Finset.sum_image fun k _ k' _ h => tauOf_injective h]

/-! ## `Amat` vanishes outside `ρ ∈ {0, …, n+1}`

`Stats.lean` gives vanishing above the superdiagonal
(`Amat_eq_zero_of_add_one_lt`); these two give vanishing off the printed
`ρ`-range `eq:def-A-range`, which is what justifies summing `ρ` over
`Finset.Icc 0 (n+1)` below. -/

theorem Amat_eq_zero_of_neg {τ ρ : ℤ} (h : ρ < 0) : Amat n τ ρ = 0 := by
  rw [Amat, card_eq_zero, filter_eq_empty_iff]
  rintro s - ⟨-, hind⟩
  omega

theorem Amat_eq_zero_of_gt {τ ρ : ℤ} (h : (n : ℤ) + 1 < ρ) :
    Amat n τ ρ = 0 := by
  rw [Amat, card_eq_zero, filter_eq_empty_iff]
  rintro s - ⟨-, hind⟩
  have := indeg_le s
  omega

/-! ## The master counting dictionary

Everything below reduces to one fact: summing a row of `A` over any set
`R` of `indeg`-values counts the members of `𝓕_n` in the corresponding
`tp`-class whose `indeg` lies in `R`.  Instantiating `R` gives both the
`uVec` and the `Tmat` dictionaries. -/

theorem sum_Amat_eq_card (n : ℕ) (τ : ℤ) (R : Finset ℤ) :
    ∑ ρ ∈ R, Amat n τ ρ =
      #((Fn n).filter fun s => top s = τ ∧ (indeg s : ℤ) ∈ R) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s : Fin (n + 1) → ℕ => (indeg s : ℤ)) (t := R)
    (fun s hs => (Finset.mem_filter.mp hs).2.2)]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [Amat, Finset.filter_filter]
  congr 1
  ext s
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hsF, htop, hind⟩
    exact ⟨hsF, ⟨htop, by rw [hind]; exact hρ⟩, hind⟩
  · rintro ⟨hsF, ⟨htop, -⟩, hind⟩
    exact ⟨hsF, htop, hind⟩

/-! ## `def-uT`: the initial vector `u⃗` and the transfer matrices `T(δ)` -/

/-- `def-uT`, first half: the row vector `u[τ] = ∑_ρ A[τ][ρ]` — the row
sums of `A`, over the supporting range `ρ ∈ {0, …, n+1}`
(`uVec_eq_sum_row` says any larger range gives the same). -/
def uVec (n : ℕ) : Fin (n + 2) → ℕ :=
  fun k => ∑ ρ ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), Amat n (tauOf k) ρ

/-- The format fact of `def-uT`: `u⃗` is the row sum of `A`, over any
range of `ρ` containing the support `{0, …, n+1}`. -/
theorem uVec_eq_sum_row (n : ℕ) (k : Fin (n + 2)) {R : Finset ℤ}
    (hR : Finset.Icc (0 : ℤ) ((n : ℤ) + 1) ⊆ R) :
    uVec n k = ∑ ρ ∈ R, Amat n (tauOf k) ρ := by
  simp only [uVec]
  refine Finset.sum_subset hR fun ρ _ hρ => ?_
  rcases lt_or_ge ρ 0 with h | h
  · exact Amat_eq_zero_of_neg h
  · refine Amat_eq_zero_of_gt ?_
    rw [Finset.mem_Icc] at hρ
    omega

/-- The counting dictionary for `u⃗` (`def-uT`): `u[τ]` counts the
`s⃗ ∈ 𝓕_n` with `tp(s⃗) = τ`. -/
theorem uVec_eq_card (n : ℕ) (k : Fin (n + 2)) :
    uVec n k = #((Fn n).filter fun s => top s = tauOf k) := by
  simp only [uVec]
  rw [sum_Amat_eq_card]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hsF, htop, -⟩
    exact ⟨hsF, htop⟩
  · rintro ⟨hsF, htop⟩
    have := indeg_le s
    exact ⟨hsF, htop, by omega, by omega⟩

/-- `def-uT`, second half: the transfer matrix
`T(δ)[τ][τ'] = ∑_{ρ > τ−δ} A[τ'][ρ]`.  **The row index `τ` is the `tp`
of the previous summand and the column index `τ'` is the `tp` of the
current one**; `ρ` is the `indeg` of the current summand and is summed
out.  Total in `δ : ℤ` (the printed definition has `δ ≥ 0`; the formula
does not need it, and totality is what makes C2a unconditional). -/
def Tmat (n : ℕ) (δ : ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℕ :=
  Matrix.of fun k k' =>
    ∑ ρ ∈ (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter (fun ρ => tauOf k - δ < ρ),
      Amat n (tauOf k') ρ

theorem Tmat_apply (n : ℕ) (δ : ℤ) (k k' : Fin (n + 2)) :
    Tmat n δ k k' =
      ∑ ρ ∈ (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter (fun ρ => tauOf k - δ < ρ),
        Amat n (tauOf k') ρ := rfl

/-- The counting dictionary for `T(δ)` (`def-uT`): `T(δ)[τ][τ']` counts
the `s⃗ ∈ 𝓕_n` with `tp(s⃗) = τ'` whose `indeg` is large enough to be
chained after a predecessor of `tp` equal to `τ`. -/
theorem Tmat_apply_eq_card (n : ℕ) (δ : ℤ) (k k' : Fin (n + 2)) :
    Tmat n δ k k' =
      #((Fn n).filter fun s => top s = tauOf k' ∧ tauOf k - δ < (indeg s : ℤ)) := by
  rw [Tmat_apply, sum_Amat_eq_card]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hsF, htop, ⟨-, -⟩, hlt⟩
    exact ⟨hsF, htop, hlt⟩
  · rintro ⟨hsF, htop, hlt⟩
    have := indeg_le s
    exact ⟨hsF, htop, ⟨by omega, by omega⟩, hlt⟩

/-! ## Chained tuples as a `Finset` -/

instance decidableChained {n r : ℕ} (d : Fin r → ℕ)
    (s : Fin r → Fin (n + 1) → ℕ) : Decidable (Chained d s) :=
  decidable_of_iff
    (∀ i j : Fin r, i.val + 1 = j.val → hatTop d s i < hatIndeg d s j)
    ⟨fun h i j hij => h i j hij, fun h _i _j hij => h hij⟩

/-- The chained locus of `thm-chaining`, as a `Finset`: tuples with
every component in `𝓕_n`, satisfying the (absolute-form) chaining
condition. -/
def chainedTuples (n r : ℕ) (d : Fin r → ℕ) :
    Finset (Fin r → Fin (n + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin r => Fn n).filter (Chained d)

theorem mem_chainedTuples {r : ℕ} {d : Fin r → ℕ}
    {s : Fin r → Fin (n + 1) → ℕ} :
    s ∈ chainedTuples n r d ↔ (∀ i, s i ∈ Fn n) ∧ Chained d s := by
  simp [chainedTuples, Fintype.mem_piFinset]

/-- The chained count refined by the `tp`-class of the **last**
component — the state vector of the transfer-matrix recursion.
`r` here is the number of *gaps*: tuples have `r + 1` components,
matching the manuscript's rank `r + 1`. -/
def chainedTopCount (n r : ℕ) (d : Fin (r + 1) → ℕ) (k : Fin (n + 2)) : ℕ :=
  #((chainedTuples n (r + 1) d).filter fun s =>
    top (s (Fin.last r)) = tauOf k)

/-! ## The ordered matrix product

The `T(δ)` do not commute, so the product is a right-peeling recursion
(matching the induction, which peels the last summand), never a
`Finset.prod`.  `Tprod n r g = T(g 0) * T(g 1) * ⋯ * T(g (r−1))`, in
increasing index order — `g i` is the manuscript's gap `δ_{i+2}`
(0-based `i`). -/

def Tprod (n : ℕ) : (r : ℕ) → (Fin r → ℤ) →
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℕ
  | 0, _ => 1
  | r + 1, g => Tprod n r (g ∘ Fin.castSucc) * Tmat n (g (Fin.last r))

@[simp] theorem Tprod_zero (n : ℕ) (g : Fin 0 → ℤ) : Tprod n 0 g = 1 := rfl

@[simp] theorem Tprod_succ (n r : ℕ) (g : Fin (r + 1) → ℤ) :
    Tprod n (r + 1) g =
      Tprod n r (g ∘ Fin.castSucc) * Tmat n (g (Fin.last r)) := rfl

/-- The gap vector: `gaps d i = d_{i+1} − d_i` as an honest
ℤ-difference (0-based; the manuscript's `δ_{i+2} = d_{i+2} − d_{i+1}`,
1-based).  No monotonicity of `d` is assumed; under `Monotone d` this
is the printed ℕ-gap (`gaps_eq_of_monotone`). -/
def gaps {r : ℕ} (d : Fin (r + 1) → ℕ) : Fin r → ℤ :=
  fun i => (d i.succ : ℤ) - d i.castSucc

theorem gaps_comp_castSucc {r : ℕ} (d : Fin (r + 2) → ℕ) :
    gaps (d ∘ Fin.castSucc) = gaps d ∘ Fin.castSucc := by
  funext i
  simp only [gaps, Function.comp_apply, Fin.succ_castSucc]

theorem gaps_last {r : ℕ} (d : Fin (r + 2) → ℕ) :
    gaps d (Fin.last r) =
      (d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc) := by
  simp only [gaps, Fin.succ_last]

/-- Under `Monotone d` (the manuscript's sortedness), the gaps are the
printed non-negative differences `δᵢ = dᵢ − dᵢ₋₁ ∈ ℕ`.  This is the
**only** place sortedness is spent in rung C2. -/
theorem gaps_eq_of_monotone {r : ℕ} {d : Fin (r + 1) → ℕ}
    (hd : Monotone d) :
    gaps d = fun i => ((d i.succ - d i.castSucc : ℕ) : ℤ) := by
  funext i
  have h : d i.castSucc ≤ d i.succ := hd (Fin.castSucc_le_succ i)
  simp only [gaps]
  omega

/-! ## The base case: one component, no matrix -/

theorem chainedTopCount_zero (n : ℕ) (d : Fin 1 → ℕ) (k : Fin (n + 2)) :
    chainedTopCount n 0 d k =
      #((Fn n).filter fun s => top s = tauOf k) := by
  simp only [chainedTopCount]
  refine Finset.card_bij' (fun s _ => s (Fin.last 0)) (fun t _ => fun _ => t)
    ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    obtain ⟨hpi, -⟩ := mem_chainedTuples.mp hs1
    exact Finset.mem_filter.mpr ⟨hpi _, hs2⟩
  · intro t ht
    obtain ⟨htF, htop⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr
      ⟨mem_chainedTuples.mpr ⟨fun _ => htF, ?_⟩, htop⟩
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

/-! ## The inductive step: peeling the last summand -/

/-- The chaining condition on a `snoc` tuple: the first `r+1` components
chained among themselves, and the appended component chained after the
last of them.  This is where `def-uT`'s row/column reading is welded to
`thm-chaining`: the *previous* top on the left of the inequality, the
*current* `indeg` on the right. -/
theorem chained_snoc_iff {r : ℕ} {d : Fin (r + 2) → ℕ}
    {s' : Fin (r + 1) → Fin (n + 1) → ℕ} {t : Fin (n + 1) → ℕ} :
    Chained d (Fin.snoc s' t) ↔
      Chained (d ∘ Fin.castSucc) s' ∧
        top (s' (Fin.last r)) + d ((Fin.last r).castSucc) <
          (indeg t : ℤ) + d (Fin.last (r + 1)) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have h1 := h (i := i.castSucc) (j := j.castSucc)
        (show i.castSucc.val + 1 = j.castSucc.val from hij)
      simp only [hatTop, hatIndeg, Fin.snoc_castSucc] at h1
      simpa only [hatTop, hatIndeg, Function.comp_apply] using h1
    · have h1 := h (i := (Fin.last r).castSucc) (j := Fin.last (r + 1))
        (show ((Fin.last r).castSucc).val + 1 = (Fin.last (r + 1)).val from rfl)
      simpa only [hatTop, hatIndeg, Fin.snoc_castSucc, Fin.snoc_last] using h1
  · rintro ⟨hc, hlast⟩ i j hij
    rcases lt_or_ge j.val (r + 1) with hj | hj
    · -- both indices in the initial segment: the condition is `hc`'s
      have hi : i.val < r + 1 := by omega
      have hie : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      have hje : j = Fin.castSucc ⟨j.val, hj⟩ := Fin.ext rfl
      rw [hie, hje]
      simp only [hatTop, hatIndeg, Fin.snoc_castSucc]
      have h2 := hc (i := ⟨i.val, hi⟩) (j := ⟨j.val, hj⟩)
        (show i.val + 1 = j.val from hij)
      simpa only [hatTop, hatIndeg, Function.comp_apply] using h2
    · -- `j` is the appended component: the condition is `hlast`
      have hjlt := j.isLt
      have hje : j = Fin.last (r + 1) := Fin.ext (show j.val = r + 1 by omega)
      have hie : i = (Fin.last r).castSucc := Fin.ext (show i.val = r by omega)
      rw [hie, hje]
      simp only [hatTop, hatIndeg, Fin.snoc_castSucc, Fin.snoc_last]
      exact hlast

/-- Componentwise membership over a `snoc` tuple. -/
theorem snoc_mem_Fn_iff {r : ℕ} {s' : Fin (r + 1) → Fin (n + 1) → ℕ}
    {t : Fin (n + 1) → ℕ} :
    (∀ i, (Fin.snoc s' t : Fin (r + 2) → Fin (n + 1) → ℕ) i ∈ Fn n) ↔
      (∀ i, s' i ∈ Fn n) ∧ t ∈ Fn n := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The last-summand splitting: chained `(r+2)`-tuples with prescribed
tops of the last two components are counted by (chained `(r+1)`-tuples
with prescribed last top) × (single members with prescribed top whose
`indeg` clears the chaining bar).  The second factor is a `Tmat` entry
by `Tmat_apply_eq_card`. -/
theorem card_chained_fiber {r : ℕ} (d : Fin (r + 2) → ℕ) (τ' τ : ℤ) :
    #(((chainedTuples n (r + 2) d).filter fun s =>
        top (s (Fin.last (r + 1))) = τ').filter fun s =>
        top (s ((Fin.last r).castSucc)) = τ) =
      #((chainedTuples n (r + 1) (d ∘ Fin.castSucc)).filter fun s' =>
          top (s' (Fin.last r)) = τ) *
        #((Fn n).filter fun t => top t = τ' ∧
            τ - ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc)) <
              (indeg t : ℤ)) := by
  rw [← Finset.card_product]
  refine Finset.card_bij'
    (fun s _ => (Fin.init s, s (Fin.last (r + 1))))
    (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_
  · -- forward: a chained tuple splits into a chained head and a valid tail
    intro s hs
    obtain ⟨hs1, hτ⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs2, hτ'⟩ := Finset.mem_filter.mp hs1
    obtain ⟨hpi, hch⟩ := mem_chainedTuples.mp hs2
    rw [← Fin.snoc_init_self s] at hch
    obtain ⟨hch', hlast⟩ := chained_snoc_iff.mp hch
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨mem_chainedTuples.mpr ⟨fun i => hpi i.castSucc, hch'⟩, hτ⟩
    · refine Finset.mem_filter.mpr ⟨hpi _, hτ', ?_⟩
      have hτeq : top (Fin.init s (Fin.last r)) = τ := hτ
      rw [hτeq] at hlast
      show τ - ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc)) <
        (indeg (s (Fin.last (r + 1))) : ℤ)
      omega
  · -- backward: `snoc` of a chained head and a valid tail is chained
    rintro ⟨s', t⟩ hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    obtain ⟨hA1, hτ⟩ := Finset.mem_filter.mp hA
    obtain ⟨hpi', hch'⟩ := mem_chainedTuples.mp hA1
    obtain ⟨htF, hτ', hbar⟩ := Finset.mem_filter.mp hB
    have hbar' : τ - ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc)) <
        (indeg t : ℤ) := hbar
    have hch : Chained d (Fin.snoc s' t) := by
      refine chained_snoc_iff.mpr ⟨hch', ?_⟩
      rw [hτ]
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_chainedTuples.mpr ⟨snoc_mem_Fn_iff.mpr ⟨hpi', htF⟩, hch⟩
    · rw [Fin.snoc_last]
      exact hτ'
    · rw [Fin.snoc_castSucc]
      exact hτ
  · intro s hs
    exact Fin.snoc_init_self s
  · rintro ⟨s', t⟩ hp
    simp only [Fin.init_snoc, Fin.snoc_last]

theorem chainedTopCount_succ {r : ℕ} (d : Fin (r + 2) → ℕ)
    (k' : Fin (n + 2)) :
    chainedTopCount n (r + 1) d k' =
      ∑ k : Fin (n + 2), chainedTopCount n r (d ∘ Fin.castSucc) k *
        Tmat n ((d (Fin.last (r + 1)) : ℤ) - d ((Fin.last r).castSucc)) k k' := by
  simp only [chainedTopCount]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s => top (s ((Fin.last r).castSucc)))
    (t := Finset.Icc (-1 : ℤ) (n : ℤ))
    (fun s _ => Finset.mem_Icc.mpr ⟨neg_one_le_top _, top_le _⟩),
    ← sum_tauOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [card_chained_fiber d (tauOf k') (tauOf k), Tmat_apply_eq_card]

/-! ## The main induction and C2a -/

theorem chainedTopCount_eq (n : ℕ) (r : ℕ) (d : Fin (r + 1) → ℕ) :
    chainedTopCount n r d = uVec n ᵥ* Tprod n r (gaps d) := by
  induction r with
  | zero =>
    funext k
    rw [Tprod_zero, Matrix.vecMul_one]
    exact (chainedTopCount_zero n d k).trans (uVec_eq_card n k).symm
  | succ r ih =>
    funext k'
    rw [chainedTopCount_succ, Tprod_succ, ← Matrix.vecMul_vecMul,
      ← gaps_comp_castSucc, ← ih (d ∘ Fin.castSucc), gaps_last]
    rfl

/-- The all-ones column vector `1⃗` of `def-uT`. -/
def onesCol (n : ℕ) : Fin (n + 2) → ℕ := fun _ => 1

theorem dotProduct_onesCol (v : Fin (n + 2) → ℕ) :
    v ⬝ᵥ onesCol n = ∑ k, v k := by
  simp [dotProduct, onesCol]

/-- **C2a, the transfer-matrix counting identity (`thm-main`, counting
half), unconditional**: the number of chained tuples over `𝓕_n` is
`u⃗ · T(δ₂) ⋯ T(δ_r) · 1⃗`, with the gaps as ℤ-differences.  No
hypothesis on `d` — in particular no sortedness — is needed; tuples
have `r + 1` components (the manuscript's rank), and `Tprod` is the
ordered product of `r` transfer matrices. -/
theorem card_chainedTuples (n r : ℕ) (d : Fin (r + 1) → ℕ) :
    #(chainedTuples n (r + 1) d) =
      uVec n ᵥ* Tprod n r (gaps d) ⬝ᵥ onesCol n := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s => top (s (Fin.last r)))
    (t := Finset.Icc (-1 : ℤ) (n : ℤ))
    (fun s _ => Finset.mem_Icc.mpr ⟨neg_one_le_top _, top_le _⟩),
    ← sum_tauOf, dotProduct_onesCol]
  exact Finset.sum_congr rfl fun k _ =>
    congrFun (chainedTopCount_eq n r d) k

/-- C2a in the manuscript's printed form: for sorted `d` the gaps are
the ℕ-differences `δᵢ = dᵢ − dᵢ₋₁ ≥ 0` of `thm-main`.  `Monotone d` is
spent **only** on this rewriting of the gaps. -/
theorem card_chainedTuples_of_monotone (n r : ℕ) {d : Fin (r + 1) → ℕ}
    (hd : Monotone d) :
    #(chainedTuples n (r + 1) d) =
      uVec n ᵥ* Tprod n r (fun i => ((d i.succ - d i.castSucc : ℕ) : ℤ)) ⬝ᵥ
        onesCol n := by
  rw [card_chainedTuples, gaps_eq_of_monotone hd]

/-! ## C2b: `thm-main` modulo the surjectivity of `thm-chaining` -/

/-- Article 2's `FF(d⃗)` (`def-fn`, `eq:auto-7`): the sums
`∑ᵢ shift^{dᵢ}(s⃗ᵢ)` over **all** tuples from `𝓕_n` — ℕ-valued in
absolute degrees, per rung C1's total-function convention (the
manuscript's vectors of length `n + d_r + 1`, extended by zero). -/
def ffSetN (n : ℕ) {r : ℕ} (d : Fin r → ℕ) : Set (ℕ → ℕ) :=
  {x | ∃ s : Fin r → Fin (n + 1) → ℕ, (∀ i, s i ∈ Fn n) ∧ Phi d s = x}

theorem coe_chainedTuples (n r : ℕ) (d : Fin r → ℕ) :
    (chainedTuples n r d : Set (Fin r → Fin (n + 1) → ℕ)) =
      {s | (∀ i, s i ∈ Fn n) ∧ Chained d s} := by
  ext s
  simp [mem_chainedTuples]

/-- **C2b: `thm-main` as printed, modulo one explicit hypothesis.**
`hsurj` is the surjectivity half of `thm-chaining` — every element of
`FF(d⃗)` is the sum of a *chained* tuple.  That half is **open
combinatorially**; its known proof is algebraic, through the Amata–Crupi
lex theory, and formalising it is rung C3, a non-target.  The paper
proves `thm-main` "modulo" the same statement, and the Lean says the
same.  Injectivity needs no hypothesis: it is rung C1's
`phi_injOn_chained`, via the explicit water-filling inverse. -/
theorem card_ffSetN (n r : ℕ) (d : Fin (r + 1) → ℕ)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ Fn n) ∧ Chained d s}
      (ffSetN n d)) :
    (ffSetN n d).ncard =
      uVec n ᵥ* Tprod n r (gaps d) ⬝ᵥ onesCol n := by
  have himg : ffSetN n d =
      Phi d '' {s | (∀ i, s i ∈ Fn n) ∧ Chained d s} := by
    refine Set.Subset.antisymm hsurj ?_
    rintro x ⟨s, ⟨hF, -⟩, rfl⟩
    exact ⟨s, hF, rfl⟩
  rw [himg, Set.InjOn.ncard_image (phi_injOn_chained n (r + 1) d),
    ← coe_chainedTuples, Set.ncard_coe_finset, card_chainedTuples]

/-- C2b in the manuscript's literally printed form (`thm-main` verbatim,
still modulo `thm-chaining`'s surjectivity): sorted `d`, gaps as the
non-negative differences `δᵢ = dᵢ − dᵢ₋₁ ∈ ℕ`. -/
theorem card_ffSetN_of_monotone (n r : ℕ) {d : Fin (r + 1) → ℕ}
    (hd : Monotone d)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ Fn n) ∧ Chained d s}
      (ffSetN n d)) :
    (ffSetN n d).ncard =
      uVec n ᵥ* Tprod n r (fun i => ((d i.succ - d i.castSucc : ℕ) : ℤ)) ⬝ᵥ
        onesCol n := by
  rw [card_ffSetN n r d hsurj, gaps_eq_of_monotone hd]

/-! ## `cor-r1`: the rank-one sanity anchor -/

/-- `cor-r1`, first equality: `∑_τ u[τ] = |𝓕_n|` — the row sums of `A`
total the whole of `𝓕_n`. -/
theorem sum_uVec (n : ℕ) : ∑ k : Fin (n + 2), uVec n k = #(Fn n) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s : Fin (n + 1) → ℕ => top s)
    (t := Finset.Icc (-1 : ℤ) (n : ℤ))
    (fun s _ => Finset.mem_Icc.mpr ⟨neg_one_le_top _, top_le _⟩),
    ← sum_tauOf]
  exact Finset.sum_congr rfl fun k _ => uVec_eq_card n k

/-- `cor-r1`: at rank one the count is `|𝓕_n|` itself (Linusson's own
count `F^n(n)`), through C2a with the empty matrix product. -/
theorem card_chainedTuples_one (n : ℕ) (d : Fin 1 → ℕ) :
    #(chainedTuples n 1 d) = #(Fn n) := by
  rw [card_chainedTuples n 0 d, Tprod_zero, Matrix.vecMul_one,
    dotProduct_onesCol, sum_uVec]

end ExteriorConvex
