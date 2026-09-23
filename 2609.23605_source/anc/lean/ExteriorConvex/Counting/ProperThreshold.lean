/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D3c of the article-2 formalisation: the proper threshold and `λ_pr`

Formalisation of `prop-proper-threshold` and the proper half of
`prop-perron-threshold` from `article/exterior-convex_article2_draft_3.org`,
per `working-notes/PLAN-formalise-D3-remaining.org` (rung D3c).

**Why the threshold is `n − 1` and not `n + 1`.**  The chaining condition
is `tp(s⃗_{i−1}) < indeg(s⃗_i) + δᵢ`.  Over `𝓕_n` the extremes are
`max tp = n` and `min indeg = 0`, so vacuity needs `δ ≥ n + 1` — that is
rung D1.  Over `S_n` the minimum initial degree is `2`, not `0`
(`SnF_eq_filter_indeg`, rung D3a), so vacuity needs `n < 2 + δ`, i.e.
`δ ≥ n − 1`.  The whole difference between the two thresholds is that one
number, and every proof below is D1's with `0` replaced by `2`.

Contents, by manuscript item:

* **`prop-proper-threshold`** — `properChainedTuples_eq_piFinset_iff`
  (the proper chained locus is the full Cartesian power `S_n^{r+1}` iff
  every gap is `≥ n − 1`, proved directly on the `Finset`),
  `card_properChainedTuples_eq_pow_iff` (the same for cardinalities),
  `ncard_ffSetPrN_eq_pow_iff` (the printed `|FF_pr(d⃗)| = |S_n|^{r+1}`
  form, modulo the same combined surjectivity/`lem-lexproper` hypothesis
  as D3a's `card_ffSetPrN`), and the sharpness clause
  `filter_not_properChained_at_sub_two`.  The saturation lemma
  `Tpmat_eq_vecMulVec_of_le` (`T′(δ) = 1⃗ u⃗′` for `δ ≥ n − 1`), its
  sharpness `Tpmat_ne_vecMulVec_at_sub_two` (`T′(n−2) ≠ 1⃗ u⃗′` for
  `n ≥ 1` — the boundary is exact, not merely sufficient), and the
  collapsed product `vecMul_Tpprod_dot_of_saturated`
  (`u⃗′ T′(δ₂)⋯T′(δ_{r+1}) 1⃗ = |S_n|^{r+1}`) give the matrix-side view.

* **The sharpness set is a product, not D1's singleton.**  At gap
  `δ = n − 2` the constraint fails iff `tp(s⃗) ≥ indeg(t⃗) + n − 2`, and
  since `tp ≤ n` and `indeg ≥ 2` on `S_n` this forces `tp(s⃗) = n` *and*
  `indeg(t⃗) = 2`, so the violating set is exactly

    `{fullVec n} ×ˢ ((SnF n).filter fun t => indeg t = 2)`.

  The first factor is a singleton (`tp = n` pins the full simplex, as in
  D1), but the second is the whole `indeg = 2` class of `S_n` — of size
  `3` at `n = 3` (namely `(1,3,m,0)` for `m = 0,1,2`), a singleton only
  at `n = 1` where it degenerates to `{fullVec 1}`.  D1's violating pair
  `(full simplex, void family)` does not transcribe: the void family is
  not proper.  Its proper replacement in the "only if" witness tuple is
  the smallest proper truncation `truncVec n 1 = (1, n, 0, …, 0)`, the
  unique member of `S_n` with `tp = 1`, `indeg = 2`.
  `card_filter_not_properChained_at_sub_two` and
  `filter_indeg_two_nonempty` record the count and the non-vacuity.

* **`prop-perron-threshold`, proper half, as an eigenvalue statement**
  (mirroring rung D4, same deliberate scope per Jan's decision of
  2026-09-17): above the threshold `δ ≥ n − 1` the matrix `T′(δ)` is
  rank one (`Tpmat_eq_vecMulVec_of_le`), it has `1⃗` as an eigenvector
  with eigenvalue `|S_n|` (`Tpmat_mulVec_onesCol_of_le`), and over ℚ
  every eigenvalue with a non-zero eigenvector is `0` or `|S_n|`
  (`eigenvalue_pr_eq_zero_or_card`).  **What is *not* formalised is the
  word "Perron"**: that `|S_n|` is the eigenvalue of largest modulus
  with a non-negative eigenvector needs Perron–Frobenius (and a spectral
  radius), which Mathlib lacks; §10.1 of the manuscript says so, and
  this file must not appear to certify it.

**On `n ≥ 1`.**  Every statement below that speaks of `S_n` carries
`1 ≤ n`, inherited from the bridge `SnF_eq_filter_indeg` — except
`eigenvalue_pr_eq_zero_or_card`, where it turned out *slack* (a
non-zero eigenvalue certifies `n ≥ 1` by itself; see its docstring).
For the threshold *iff* the hypothesis is genuinely load-bearing, not
inherited:
at `n = 0` the proper chained locus is empty (no member of `𝓕_0` has
`indeg ≥ 2`) while `S_0 = {(1)}` is not, and even the `indeg`-form
equivalence fails there (`∅ = ∅` holds at every gap, while the printed
condition `δ ≥ −1` does not).  The saturation
`Tpmat_eq_vecMulVec_of_le` alone is unconditional (at `n = 0` both sides
are the zero matrix).  All thresholds are stated over ℤ
(`(n : ℤ) − 1 ≤ δ`), so the ℕ-subtraction in the printed `n − 1` never
truncates: at `n = 1` the threshold honestly reads `δ ≥ 0`, and the
`n = 0` corner where ℕ-truncation would diverge from ℤ is excluded by
`1 ≤ n` anyway.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`); the sanity anchors — `u⃗′ = (0,0,1,3,1)` and
`|S_3| = 5` entrywise, the saturation boundary `T′(2) = 1⃗u⃗′` but
`T′(1) ≠ 1⃗u⃗′` at `n = 3` (exactly `δ = n − 1`, not `δ = n − 2`), the
proper pair counts `25`/`22` at `δ = 2`/`1` and the triple counts
`125`/`95` at `δ = (2,2)`/`(1,1)` (each by `Finset` enumeration *and*
by the matrix product, agreeing), the three-element violating set at
`n = 3`, the `n = 2` boundary `4`/`3` at `δ = 1`/`0` (`eq:auto-18`/
`eq:auto-17`), and `|FF_pr(2; 0^r)| = r + 1` — were `#eval`s during
development (recorded in `runs/properthreshold-lean-anchors-20260918.md`)
and stay out of the formal statements, deliberately.
-/
import ExteriorConvex.Counting.Structure
import ExteriorConvex.Counting.Proper

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## The two witnesses: the full simplex and the smallest proper
truncation are members of `S_n` -/

/-- The full simplex is proper: `indeg (fullVec n) = n + 1 ≥ 2` for
`n ≥ 1`. -/
theorem fullVec_mem_SnF (hn : 1 ≤ n) : fullVec n ∈ SnF n := by
  rw [SnF_eq_filter_indeg hn]
  refine Finset.mem_filter.mpr ⟨fullVec_mem_Fn, ?_⟩
  rw [indeg_fullVec]
  omega

/-- The smallest proper truncation `truncVec n 1 = (1, n, 0, …, 0)` — the
full `1`-skeleton, the proper replacement for D1's void-family witness
(the void family has `indeg = 0` and is *not* proper). -/
theorem truncVec_one_mem_SnF (hn : 1 ≤ n) : truncVec n 1 ∈ SnF n := by
  rw [SnF_eq_filter_indeg hn]
  refine Finset.mem_filter.mpr ⟨truncVec_mem_Fn 1, ?_⟩
  rw [indeg_truncVec hn]

/-! ## Saturation: `T′(δ) = 1⃗ u⃗′` for `δ ≥ n − 1` -/

/-- Saturation above the proper threshold: for `δ ≥ n − 1` the chaining
condition `ρ > τ − δ` is vacuous *on the support of `A′`* (`ρ ≥ 2`,
since `τ − δ ≤ n − (n−1) = 1 < 2`), so every row of `T′(δ)` is `u⃗′`:
`T′(δ) = 1⃗ u⃗′`, manifestly of rank one.  This is the matrix engine
behind both `prop-proper-threshold` and the proper half of
`prop-perron-threshold`.  No hypothesis on `n`: at `n = 0` both sides
are the zero matrix. -/
theorem Tpmat_eq_vecMulVec_of_le {δ : ℤ} (h : (n : ℤ) - 1 ≤ δ) :
    Tpmat n δ = vecMulVec (onesCol n) (upVec n) := by
  ext k k'
  have hsum : ∑ ρ ∈ (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter
      (fun ρ => tauOf k - δ < ρ), Apmat n (tauOf k') ρ =
        ∑ ρ ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), Apmat n (tauOf k') ρ := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun ρ hρ hno => ?_
    refine Apmat_eq_zero_of_lt ?_
    have h1 := tauOf_le k
    have h2 : ¬ (tauOf k - δ < ρ) := fun hc =>
      hno (Finset.mem_filter.mpr ⟨hρ, hc⟩)
    omega
  rw [Tpmat_apply, hsum, vecMulVec_apply]
  simp only [onesCol, upVec, one_mul]

/-- The threshold is exact on the matrix side: at `δ = n − 2` the
saturation fails, for every `n ≥ 1`.  Witness entry: row `τ = n`,
column `τ' = 1`, where `T′(n−2)[n][1] = 0` (the bar `ρ > 2` excludes
the whole column-`1` support of `A′`, namely `A′[1][2] = 1`) while
`(1⃗ u⃗′)[n][1] = u′[1] = 1`. -/
theorem Tpmat_ne_vecMulVec_at_sub_two (hn : 1 ≤ n) :
    Tpmat n ((n : ℤ) - 2) ≠ vecMulVec (onesCol n) (upVec n) := by
  intro hcontra
  have h2n : (2 : ℕ) < n + 2 := by omega
  have hlast : tauOf (Fin.last (n + 1)) = (n : ℤ) := by
    simp only [tauOf, Fin.val_last]
    omega
  have htau : tauOf (⟨2, h2n⟩ : Fin (n + 2)) = 1 := by
    show ((2 : ℕ) : ℤ) - 1 = 1
    norm_num
  have hL : Tpmat n ((n : ℤ) - 2) (Fin.last (n + 1)) ⟨2, h2n⟩ = 0 := by
    rw [Tpmat_apply]
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    have hρ2 := (Finset.mem_filter.mp hρ).2
    rw [hlast] at hρ2
    rw [htau]
    exact Apmat_eq_zero_of_add_one_lt (by omega)
  have hR : vecMulVec (onesCol n) (upVec n) (Fin.last (n + 1)) ⟨2, h2n⟩ =
      1 := by
    rw [vecMulVec_apply]
    simp only [onesCol, one_mul, upVec]
    rw [Finset.sum_eq_single (2 : ℤ)]
    · have hsup := Amat_superdiag n (j := 1) hn
      norm_num at hsup
      rw [htau, Apmat_eq_of_le (by norm_num)]
      exact hsup
    · intro ρ _ hne
      rw [htau]
      rcases lt_or_ge ρ 2 with hl | hg
      · exact Apmat_eq_zero_of_lt hl
      · exact Apmat_eq_zero_of_add_one_lt (by omega)
    · intro hmem
      exact absurd (Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩) hmem
  rw [hcontra, hR] at hL
  exact one_ne_zero hL

/-! ## `prop-proper-threshold`: the equivalence on the `Finset` -/

/-- `prop-proper-threshold`, the equivalence, proved directly on the
`Finset`: the proper chained locus exhausts the full Cartesian power
`S_n^{r+1}` **iff** every gap is at least `n − 1`.  Stated for arbitrary
(not necessarily sorted) `d`, with the gaps as honest ℤ-differences.

`1 ≤ n` is **genuinely load-bearing here, not inherited**: at `n = 0`
the proper chained locus is empty while `S_0^{r+1}` is not, and even the
`indeg`-form equivalence fails (`∅ = ∅` at every gap, against a
condition `δ ≥ −1` that unsorted `d` can violate). -/
theorem properChainedTuples_eq_piFinset_iff (n r : ℕ) (hn : 1 ≤ n)
    (d : Fin (r + 1) → ℕ) :
    properChainedTuples n (r + 1) d =
        Fintype.piFinset (fun _ : Fin (r + 1) => SnF n) ↔
      ∀ i : Fin r, (n : ℤ) - 1 ≤ gaps d i := by
  rw [properChainedTuples_eq_filter_SnF hn]
  constructor
  · -- only if: exhibit the excluded tuple at a small gap.  D1's tuple
    -- `(fullVec, …, 0⃗, …)` does not transcribe (the void family is not
    -- proper); the proper tail is the smallest truncation `truncVec n 1`.
    intro heq
    by_contra hgap
    obtain ⟨i, hi⟩ := not_forall.mp hgap
    have hmem : (fun j : Fin (r + 1) =>
        if j.val ≤ i.val then fullVec n else truncVec n 1) ∈
          Fintype.piFinset (fun _ : Fin (r + 1) => SnF n) := by
      rw [Fintype.mem_piFinset]
      intro j
      split_ifs
      · exact fullVec_mem_SnF hn
      · exact truncVec_one_mem_SnF hn
    rw [← heq] at hmem
    have hch := (Finset.mem_filter.mp hmem).2
    have hcon := hch (i := i.castSucc) (j := i.succ)
      (by simp [Fin.val_succ, Fin.val_castSucc])
    simp only [hatTop, hatIndeg, Fin.val_castSucc, Fin.val_succ] at hcon
    split_ifs at hcon <;>
      first
        | omega
        | · rw [top_fullVec, indeg_truncVec hn] at hcon
            simp only [gaps] at hi
            omega
  · -- if: with every gap `≥ n−1` the constraint holds for any
    -- `S_n`-tuple, since `tp ≤ n` and `indeg ≥ 2` there
    intro hgap
    refine Finset.Subset.antisymm (Finset.filter_subset _ _) ?_
    intro s hsmem
    refine Finset.mem_filter.mpr ⟨hsmem, ?_⟩
    intro a b hab
    have ha : a.val < r := by
      have := b.isLt
      omega
    have hg := hgap ⟨a.val, ha⟩
    simp only [gaps] at hg
    have hcs : (⟨a.val, ha⟩ : Fin r).castSucc = a := Fin.ext rfl
    have hsc : (⟨a.val, ha⟩ : Fin r).succ = b := Fin.ext hab
    rw [hcs, hsc] at hg
    have hsb := Fintype.mem_piFinset.mp hsmem b
    rw [SnF_eq_filter_indeg hn, Finset.mem_filter] at hsb
    simp only [hatTop, hatIndeg]
    have h1 := top_le (s a)
    have h2 : 2 ≤ indeg (s b) := hsb.2
    omega

/-- The proper chained locus sits inside the power `S_n^r`. -/
theorem properChainedTuples_subset_piFinset (hn : 1 ≤ n) (r : ℕ)
    (d : Fin r → ℕ) :
    properChainedTuples n r d ⊆
      Fintype.piFinset (fun _ : Fin r => SnF n) := by
  rw [properChainedTuples_eq_filter_SnF hn]
  exact Finset.filter_subset _ _

/-- `prop-proper-threshold` for cardinalities:
`#(proper chained tuples) = |S_n|^{r+1}` iff every gap is at least
`n − 1`.  Cardinality equality forces set equality since the proper
chained locus sits inside the power. -/
theorem card_properChainedTuples_eq_pow_iff (n r : ℕ) (hn : 1 ≤ n)
    (d : Fin (r + 1) → ℕ) :
    #(properChainedTuples n (r + 1) d) = #(SnF n) ^ (r + 1) ↔
      ∀ i : Fin r, (n : ℤ) - 1 ≤ gaps d i := by
  rw [← properChainedTuples_eq_piFinset_iff n r hn d]
  have hcard : #(Fintype.piFinset (fun _ : Fin (r + 1) => SnF n)) =
      #(SnF n) ^ (r + 1) := by
    rw [Fintype.card_piFinset]
    simp
  constructor
  · intro h
    exact Finset.eq_of_subset_of_card_le
      (properChainedTuples_subset_piFinset hn (r + 1) d) (by omega)
  · intro h
    rw [h, hcard]

/-- `prop-proper-threshold` as printed
(`|FF_pr(d⃗)| = |S_n|^{r+1}` iff all gaps `≥ n − 1`), modulo the same
explicit hypothesis as D3a's `card_ffSetPrN` — covering both the
surjectivity half of `thm-chaining` (rung C3, a non-target) and
`lem-lexproper` (Amata–Crupi lex algebra, out of scope for the same
reason). -/
theorem ncard_ffSetPrN_eq_pow_iff (n r : ℕ) (hn : 1 ≤ n)
    (d : Fin (r + 1) → ℕ)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ SnF n) ∧ Chained d s}
      (ffSetPrN n d)) :
    (ffSetPrN n d).ncard = #(SnF n) ^ (r + 1) ↔
      ∀ i : Fin r, (n : ℤ) - 1 ≤ gaps d i := by
  rw [card_ffSetPrN n r hn d hsurj, ← card_properChainedTuples]
  exact card_properChainedTuples_eq_pow_iff n r hn d

/-! ## The sharpness clause: the violating set at `δ = n − 2` is a
product, not a singleton -/

/-- `prop-proper-threshold`, sharpness clause: at gap `δ = n − 2` the
chaining constraint `tp(s⃗) < indeg(t⃗) + δ` fails on `S_n × S_n` for
**exactly** the pairs in `{full simplex} × {indeg = 2 class}` — a
product whose first factor is a singleton (`tp = n` pins the full
simplex) but whose second is the whole `indeg = 2` class of `S_n`,
which has more than one element for `n ≥ 2` (at `n = 3` it is
`{(1,3,0,0), (1,3,1,0), (1,3,2,0)}`).  Contrast D1's
`filter_not_chained_at_n`, whose violating set is the singleton
`{(full simplex, void family)}`: the void family is not proper, and its
absence is exactly what widens the failure to a full class here. -/
theorem filter_not_properChained_at_sub_two (n : ℕ) (hn : 1 ≤ n) :
    (((SnF n) ×ˢ (SnF n)).filter fun p =>
        ¬ top p.1 < (indeg p.2 : ℤ) + ((n : ℤ) - 2)) =
      {fullVec n} ×ˢ ((SnF n).filter fun t => indeg t = 2) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
    not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, hle⟩
    have h1' : p.1 ∈ Fn n ∧ 2 ≤ indeg p.1 := by
      rw [SnF_eq_filter_indeg hn, Finset.mem_filter] at h1
      exact h1
    have h2' : p.2 ∈ Fn n ∧ 2 ≤ indeg p.2 := by
      rw [SnF_eq_filter_indeg hn, Finset.mem_filter] at h2
      exact h2
    have ht := top_le p.1
    have hind : indeg p.2 = 2 := by omega
    have htop : top p.1 = (n : ℤ) := by omega
    exact ⟨eq_fullVec_of_top_eq_n h1'.1 htop, h2, hind⟩
  · rintro ⟨hfull, h2, hind⟩
    refine ⟨⟨?_, h2⟩, ?_⟩
    · rw [hfull]
      exact fullVec_mem_SnF hn
    · rw [hfull, top_fullVec, hind]
      omega

/-- The size of the violating set at `δ = n − 2` is the size of the
`indeg = 2` class of `S_n` — the entry `∑_τ A′[τ][2]` in matrix terms,
`3` at `n = 3`. -/
theorem card_filter_not_properChained_at_sub_two (n : ℕ) (hn : 1 ≤ n) :
    #(((SnF n) ×ˢ (SnF n)).filter fun p =>
        ¬ top p.1 < (indeg p.2 : ℤ) + ((n : ℤ) - 2)) =
      #((SnF n).filter fun t => indeg t = 2) := by
  rw [filter_not_properChained_at_sub_two n hn, Finset.card_product,
    Finset.card_singleton, one_mul]

/-- The `indeg = 2` class of `S_n` is non-empty for every `n ≥ 1`
(witness: the smallest proper truncation), so the sharpness clause is
never vacuous — `δ = n − 2` genuinely fails, and the threshold `n − 1`
of `prop-proper-threshold` is exact at every `n ≥ 1`, including `n = 1`
where it reads `δ ≥ 0`. -/
theorem filter_indeg_two_nonempty (hn : 1 ≤ n) :
    ((SnF n).filter fun t => indeg t = 2).Nonempty := by
  refine ⟨truncVec n 1, Finset.mem_filter.mpr
    ⟨truncVec_one_mem_SnF hn, ?_⟩⟩
  rw [indeg_truncVec hn]

/-! ## The collapsed product: `u⃗′ T′(δ₂)⋯T′(δ_{r+1}) 1⃗ = |S_n|^{r+1}` -/

/-- The saturated proper bilinear form absorbs one factor:
`w⃗ (1⃗ u⃗′) 1⃗ = (w⃗ · 1⃗) · #{s⃗ ∈ 𝓕_n : indeg ≥ 2}`. -/
theorem vecMul_proper_saturated_dot (w : Fin (n + 2) → ℕ) :
    w ᵥ* vecMulVec (onesCol n) (upVec n) ⬝ᵥ onesCol n =
      (w ⬝ᵥ onesCol n) * #((Fn n).filter fun s => 2 ≤ indeg s) := by
  have hrow : ∀ k', (w ᵥ* vecMulVec (onesCol n) (upVec n)) k' =
      (w ⬝ᵥ onesCol n) * upVec n k' := by
    intro k'
    simp only [Matrix.vecMul, dotProduct, vecMulVec_apply, onesCol,
      mul_one, one_mul, Finset.sum_mul]
  rw [dotProduct_onesCol]
  calc ∑ k', (w ᵥ* vecMulVec (onesCol n) (upVec n)) k'
      = ∑ k', (w ⬝ᵥ onesCol n) * upVec n k' :=
        Finset.sum_congr rfl fun k' _ => hrow k'
    _ = (w ⬝ᵥ onesCol n) * ∑ k', upVec n k' := by
        rw [Finset.mul_sum]
    _ = (w ⬝ᵥ onesCol n) * #((Fn n).filter fun s => 2 ≤ indeg s) := by
        rw [sum_upVec]

/-- `prop-proper-threshold`, matrix side: with every gap `≥ n − 1` the
proper transfer product collapses,
`u⃗′ T′(δ₁)⋯T′(δ_r) 1⃗ = |S_n|^{r+1}` — the rank-one factor absorbs one
power of `|S_n|` per step. -/
theorem vecMul_Tpprod_dot_of_saturated (n r : ℕ) (hn : 1 ≤ n)
    {g : Fin r → ℤ} (hg : ∀ i, (n : ℤ) - 1 ≤ g i) :
    upVec n ᵥ* Tpprod n r g ⬝ᵥ onesCol n = #(SnF n) ^ (r + 1) := by
  induction r with
  | zero =>
    rw [Tpprod_zero, Matrix.vecMul_one, dotProduct_onesCol,
      sum_upVec_eq_card_SnF hn, pow_one]
  | succ r ih =>
    rw [Tpprod_succ, ← Matrix.vecMul_vecMul,
      Tpmat_eq_vecMulVec_of_le (hg (Fin.last r)),
      vecMul_proper_saturated_dot, ← SnF_eq_filter_indeg hn,
      ih (g := g ∘ Fin.castSucc) (fun i => hg i.castSucc), ← pow_succ]

/-! ## `prop-perron-threshold`, proper half, as an eigenvalue statement

**Scope note (deliberate, per the plan's decision of 2026-09-17, exactly
as rung D4's improper half).**  What is formalised is the *eigenvalue
restatement*: above the threshold `δ ≥ n − 1` the matrix `T′(δ)` is rank
one (`Tpmat_eq_vecMulVec_of_le`), it has `1⃗` as an eigenvector with
eigenvalue `|S_n|` (`Tpmat_mulVec_onesCol_of_le`), and over ℚ every
eigenvalue with a non-zero eigenvector is `0` or `|S_n|`
(`eigenvalue_pr_eq_zero_or_card`).  **What is *not* formalised is the
word "Perron"** — that `|S_n|` is the eigenvalue of largest modulus with
a non-negative eigenvector needs the Perron–Frobenius theory (and a
spectral radius) that Mathlib currently lacks.  The printed
proposition's "Perron root" wording is therefore not certified as
printed; in the rank-one case the loss is only the comparison of `|S_n|`
against `0`. -/

/-- D3c, the eigenvector: above the proper threshold `1⃗` is an
eigenvector of `T′(δ)` with eigenvalue `|S_n|` — over ℕ already. -/
theorem Tpmat_mulVec_onesCol_of_le (hn : 1 ≤ n) {δ : ℤ}
    (h : (n : ℤ) - 1 ≤ δ) :
    Tpmat n δ *ᵥ onesCol n = #(SnF n) • onesCol n := by
  funext k
  rw [Tpmat_eq_vecMulVec_of_le h]
  have hl : (vecMulVec (onesCol n) (upVec n) *ᵥ onesCol n) k =
      ∑ j, upVec n j := by
    simp [Matrix.mulVec, dotProduct, vecMulVec_apply, onesCol]
  rw [hl, sum_upVec_eq_card_SnF hn]
  simp [onesCol]

/-- The ℚ-cast of the saturated proper matrix: still `1⃗ u⃗′`. -/
theorem Tpmat_map_ratCast_of_le {δ : ℤ} (h : (n : ℤ) - 1 ≤ δ) :
    (Tpmat n δ).map (Nat.cast : ℕ → ℚ) =
      vecMulVec (fun _ => 1) (fun k => (upVec n k : ℚ)) := by
  rw [Tpmat_eq_vecMulVec_of_le h]
  ext k k'
  simp [Matrix.map_apply, vecMulVec_apply, onesCol]

/-- D3c, the "only non-zero eigenvalue" content: over ℚ, any eigenvalue
of the saturated proper transfer matrix with a non-zero eigenvector is
`0` or `|S_n|`.  (The rank-one factorisation forces every eigenvector
with non-zero eigenvalue to be constant.)

**A finding of the formalisation: no `n ≥ 1` hypothesis is needed**,
unlike every other `S_n`-facing statement of this rung — a non-zero
eigenvalue equals `#{s⃗ ∈ 𝓕_n : indeg ≥ 2}`, so its non-vanishing makes
that class non-empty, which itself forces `n ≥ 1` and hence the bridge
to `|S_n|`; at `n = 0` the saturated `T′` is the zero matrix and only
`μ = 0` occurs, so the dichotomy holds there too.  This mirrors D4's
`eigenvalue_eq_zero_or_card`, which likewise carries no side
hypothesis. -/
theorem eigenvalue_pr_eq_zero_or_card {δ : ℤ}
    (h : (n : ℤ) - 1 ≤ δ) {μ : ℚ} {v : Fin (n + 2) → ℚ} (hv : v ≠ 0)
    (heig : (Tpmat n δ).map (Nat.cast : ℕ → ℚ) *ᵥ v = μ • v) :
    μ = 0 ∨ μ = (#(SnF n) : ℚ) := by
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  · right
    rw [Tpmat_map_ratCast_of_le h] at heig
    set c : ℚ := (fun k => (upVec n k : ℚ)) ⬝ᵥ v with hc
    have hconst : ∀ k, μ * v k = c := by
      intro k
      have hk := congrFun heig k
      simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, one_mul,
        Pi.smul_apply, smul_eq_mul] at hk
      rw [hc]
      simp only [dotProduct]
      exact hk.symm
    have hvk : ∀ k, v k = c / μ := by
      intro k
      rw [eq_div_iff hμ, mul_comm]
      exact hconst k
    have hcne : c ≠ 0 := by
      intro h0
      apply hv
      funext k
      rw [hvk k, h0, zero_div]
      rfl
    have hsum : c = (c / μ) *
        (#((Fn n).filter fun s => 2 ≤ indeg s) : ℚ) := by
      calc c = ∑ k, (upVec n k : ℚ) * v k := by rw [hc, dotProduct]
        _ = ∑ k, (upVec n k : ℚ) * (c / μ) :=
            Finset.sum_congr rfl fun k _ => by rw [hvk k]
        _ = (∑ k, (upVec n k : ℚ)) * (c / μ) := by
            rw [Finset.sum_mul]
        _ = (#((Fn n).filter fun s => 2 ≤ indeg s) : ℚ) * (c / μ) := by
            rw [← Nat.cast_sum, sum_upVec]
        _ = _ := mul_comm _ _
    have hμfil : μ = (#((Fn n).filter fun s => 2 ≤ indeg s) : ℚ) := by
      field_simp at hsum
      linarith [hsum]
    -- a non-zero eigenvalue certifies `n ≥ 1`: the `indeg ≥ 2` class it
    -- counts is non-empty, and `indeg ≤ n + 1` forces `2 ≤ n + 1`
    have hne : ((Fn n).filter fun s => 2 ≤ indeg s).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      rw [hemp] at hμfil
      simp only [Finset.card_empty, Nat.cast_zero] at hμfil
      exact hμ hμfil
    obtain ⟨s, hs⟩ := hne
    have hs2 := (Finset.mem_filter.mp hs).2
    have hle := indeg_le s
    have hn : 1 ≤ n := by omega
    rw [SnF_eq_filter_indeg hn]
    exact hμfil

end ExteriorConvex
