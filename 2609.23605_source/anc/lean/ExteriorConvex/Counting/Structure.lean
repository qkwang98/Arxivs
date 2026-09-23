/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D1 of the article-2 formalisation: structure of `A`, the threshold, the normal form

Formalisation of `lem-A-structure`, `prop-threshold` and `prop-normalform`
from `article/exterior-convex_article2_draft_3.org`, per
`working-notes/PLAN-formalise-article2.org` (rung D1), together with rung
D4's eigenvalue restatement of `prop-perron-threshold` (improper half
only — see the scope note at the D4 section below).

Contents, by manuscript item:

* **`lem-A-structure`** — `Amat_superdiag` (`A[j][j+1] = 1`, with
  `filter_superdiag_eq` exhibiting the *unique* witness, the full
  truncation `truncVec n j`); `Amat_diag`
  (`A[j][j] = C(n,j) − 1`, via an explicit bijection with
  `Icc 1 (C(n,j) − 1)`); `Amat_zero_zero` (`A[0][0] = 0`); and
  `Amat_row_void_eq_zero` (row `τ = −1` vanishes off `ρ = 0`; the entry
  `A[−1][0] = 1` itself is rung A's `Amat_corner_void`).  A finding of
  the formalisation: the diagonal formula holds at `j = 0` as well,
  `A[0][0] = C(n,0) − 1 = 0`, so the manuscript's separate third claim
  is the `j = 0` case of its second.
* **`prop-threshold`** — `chainedTuples_eq_piFinset_iff` (the chained
  locus is the full Cartesian power iff every gap is `≥ n+1`, proved
  directly on the `Finset`), `card_chainedTuples_eq_pow_iff` (the same
  for cardinalities), `ncard_ffSetN_eq_pow_iff` (the printed `|FF(d⃗)|`
  form, modulo the same surjectivity hypothesis as C2b), and the
  sharpness clause `filter_not_chained_at_n`: at gap `δ = n` the
  constraint fails for **exactly one** pair,
  `(full simplex, void family)`.  The saturation lemma
  `Tmat_eq_vecMulVec_of_le` (`T(δ) = 1⃗ u⃗` for `δ ≥ n+1`) and the
  collapsed product `vecMul_Tprod_dot_of_saturated`
  (`u⃗ T(δ₂)⋯T(δ_{r+1}) 1⃗ = |𝓕_n|^{r+1}`) give the matrix-side view.
* **`prop-normalform`** — `Pmat` (the saturating one-step shift; in the
  `Fin (n+2)` indexing of `Transfer.lean` the manuscript's
  `τ' = max(τ−1, −1)` is *truncated ℕ-subtraction on the index*,
  `k' = k − 1`, so the clamp costs nothing), `Pmat_pow_apply`
  (`P^δ` sends `k` to `k − δ`, clamped), `Tmat_eq_Pmat_pow_mul`
  (`T(δ) = P^δ B`, `B = T(0)`, for `δ : ℕ` — the printed `δ ≥ 0`),
  `uVec_eq_single_vecMul` (`u⃗ = e_{−1}ᵀ B`), and
  `card_chainedTuples_normalform` (the fully factored product of
  `eq:normalform`, via `PBprod`).

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`); the entrywise sanity checks of `A`, `u⃗`, `T(0)`,
`T(1)`, `T(4)` at `n = 3` against `ex-A`/`ex-uT`, and of `P`'s powers,
were `#eval`s during development and stay out of the formal statements,
deliberately.
-/
import ExteriorConvex.Counting.Transfer

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## Locating the statistics

Two small helpers used throughout: pinning `tp` from below and above, and
the two extreme classes of `𝓕_n`. -/

/-- Locating `tp`: a positive entry at `j` and vanishing above `j` pin
`tp = j`.  (No membership in `𝓕_n` needed.) -/
theorem top_eq_of_pos_of_zero {s : Fin (n + 1) → ℕ} {j : ℕ} (hj : j ≤ n)
    (hpos : 0 < s ⟨j, Nat.lt_succ_of_le hj⟩)
    (hzero : ∀ i : Fin (n + 1), j < i.val → s i = 0) :
    top s = (j : ℤ) := by
  have h1 : (j : ℤ) ≤ top s := le_top_of_pos hpos
  have h2 : top s ≤ (j : ℤ) := by
    rcases lt_or_ge ((j : ℤ)) (top s) with hlt | hge
    · obtain ⟨i, hi, hipos⟩ := exists_apply_pos_of_top_nonneg
        (le_trans (Int.natCast_nonneg j) hlt.le)
      rw [hzero i (by omega)] at hipos
      omega
    · exact hge
  omega

/-- Over `𝓕_n`, `tp = n` pins the full simplex: a face of cardinality `n`
forces the full count in degree `n`, and fullness propagates down. -/
theorem eq_fullVec_of_top_eq_n {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n)
    (h : top s = (n : ℤ)) : s = fullVec n := by
  have hpos : 0 < s ⟨n, Nat.lt_succ_self n⟩ :=
    apply_pos_of_le_top hs (show ((n : ℕ) : ℤ) ≤ top s by omega)
  obtain ⟨D, hD, rfl⟩ := mem_Fn.mp hs
  have hfull : fEntry D n = n.choose n := by
    have hle := fEntry_le_choose D n
    have hpos' : 0 < fEntry D n := hpos
    rw [Nat.choose_self] at hle ⊢
    omega
  funext i
  show fEntry D i.val = fullVec n i
  rw [show fullVec n i = n.choose i.val from rfl]
  exact fEntry_eq_choose_of_le hD i.is_le (le_refl n) hfull

/-- Over `𝓕_n`, `indeg = 0` pins the void family: a deficiency in degree
`0` means no empty face, hence no face at all. -/
theorem eq_zero_of_indeg_eq_zero {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n)
    (h : indeg s = 0) : s = 0 := by
  have h0 : s ⟨0, Nat.succ_pos n⟩ = 0 := by
    have hlt : s ⟨0, Nat.succ_pos n⟩ < n.choose 0 :=
      apply_lt_choose_of_indeg_le hs (show indeg s ≤ 0 by omega)
    rw [Nat.choose_zero_right] at hlt
    omega
  rw [← top_eq_neg_one_iff]
  rcases lt_or_ge (top s) 0 with hlt | hge
  · have := neg_one_le_top s
    omega
  · exfalso
    have := apply_pos_of_le_top (m := ⟨0, Nat.succ_pos n⟩) hs
      (by show ((0 : ℕ) : ℤ) ≤ top s; omega)
    omega

/-! ## The full truncation and the superdiagonal of `A`
(`lem-A-structure`, first claim) -/

/-- The full truncation at `j`: the `f`-vector of the order ideal of
*all* subsets of size `≤ j` (the `j`-skeleton of the full simplex),
`(C(n,0), …, C(n,j), 0, …, 0)`. -/
def truncVec (n j : ℕ) : Fin (n + 1) → ℕ :=
  fun i => if i.val ≤ j then n.choose i.val else 0

theorem truncVec_mem_Fn (j : ℕ) : truncVec n j ∈ Fn n := by
  refine mem_Fn.mpr ⟨univ.filter fun s => #s ≤ j, ?_, ?_⟩
  · intro s t hs hts
    exact mem_filter.mpr
      ⟨mem_univ t, le_trans (card_le_card hts) (mem_filter.mp hs).2⟩
  · funext i
    simp only [fvecN_apply, fEntry, filter_filter, truncVec]
    by_cases hij : i.val ≤ j
    · rw [ite_eq_left hij]
      have h : (univ.filter fun s : Finset (Fin n) => #s ≤ j ∧ #s = i.val) =
          univ.filter fun s : Finset (Fin n) => #s = i.val := by
        ext s
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun hp => hp.2, fun hp => ⟨by omega, hp⟩⟩
      rw [h]
      exact fEntry_univ i.val
    · rw [ite_eq_right hij, card_eq_zero, filter_eq_empty_iff]
      rintro s - ⟨h1, h2⟩
      omega

theorem top_truncVec {j : ℕ} (hj : j ≤ n) : top (truncVec n j) = (j : ℤ) := by
  refine top_eq_of_pos_of_zero hj ?_ ?_
  · show 0 < if j ≤ j then n.choose j else 0
    rw [ite_eq_left (le_refl j)]
    exact Nat.choose_pos hj
  · intro i hi
    simp only [truncVec]
    rw [ite_eq_right (by omega)]

theorem indeg_truncVec {j : ℕ} (hj : j ≤ n) :
    indeg (truncVec n j) = j + 1 := by
  have h1 : j + 1 ≤ indeg (truncVec n j) := by
    rw [le_indeg_iff (by omega)]
    intro i hi
    simp only [truncVec]
    rw [ite_eq_left (by omega)]
  have h2 : indeg (truncVec n j) ≤ j + 1 := by
    rcases lt_or_ge j n with hjn | hjn
    · have h0 : truncVec n j ⟨j + 1, by omega⟩ = 0 := by
        simp only [truncVec]
        rw [ite_eq_right (by omega)]
      exact indeg_le_of_lt (j := ⟨j + 1, by omega⟩)
        (by rw [h0]; exact Nat.choose_pos (by omega))
    · have := indeg_le (truncVec n j)
      omega
  omega

/-- `lem-A-structure`, superdiagonal rigidity: `tp = j` and
`indeg = j + 1` force the full truncation at `j`. -/
theorem eq_truncVec_of_top_eq_of_indeg_eq {s : Fin (n + 1) → ℕ}
    (hs : s ∈ Fn n) {j : ℕ} (htop : top s = (j : ℤ))
    (hind : indeg s = j + 1) : s = truncVec n j := by
  funext i
  simp only [truncVec]
  by_cases hij : i.val ≤ j
  · rw [ite_eq_left hij]
    exact apply_eq_choose_of_lt_indeg hs (by omega)
  · rw [ite_eq_right hij]
    exact apply_eq_zero_of_top_lt (by omega)

/-- The superdiagonal class is the singleton `{truncVec n j}` — the
"unique witness" clause of `lem-A-structure`. -/
theorem filter_superdiag_eq (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    ((Fn n).filter fun s => top s = (j : ℤ) ∧ (indeg s : ℤ) = (j : ℤ) + 1) =
      {truncVec n j} := by
  ext s
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hsF, htop, hind⟩
    exact eq_truncVec_of_top_eq_of_indeg_eq hsF htop (by omega)
  · rintro rfl
    refine ⟨truncVec_mem_Fn j, top_truncVec hj, ?_⟩
    rw [indeg_truncVec hj]
    omega

/-- `lem-A-structure`, first claim: `A[j][j+1] = 1` for `0 ≤ j ≤ n`. -/
theorem Amat_superdiag (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    Amat n (j : ℤ) ((j : ℤ) + 1) = 1 := by
  rw [Amat, filter_superdiag_eq n hj, card_singleton]

/-! ## The diagonal of `A` (`lem-A-structure`, second claim) -/

/-- Realisation half of the diagonal count: for `1 ≤ m < C(n,j)` there is
a member of `𝓕_n` with `tp = indeg = j` and `j`-entry exactly `m` —
adjoin any `m` of the `j`-subsets to the full `(j−1)`-skeleton, which
stays an order ideal because every `(j−1)`-subset is already present. -/
theorem exists_mem_Fn_diag {j m : ℕ} (hjn : j ≤ n) (hm1 : 1 ≤ m)
    (hm2 : m < n.choose j) :
    ∃ s ∈ Fn n, top s = (j : ℤ) ∧ indeg s = j ∧
      s ⟨j, Nat.lt_succ_of_le hjn⟩ = m := by
  obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq
    (show m ≤ #(univ.powersetCard j : Finset (Finset (Fin n))) by
      rw [card_powersetCard, card_univ, Fintype.card_fin]
      omega)
  have hMj : ∀ t ∈ M, #t = j := fun t ht =>
    (Finset.mem_powersetCard.mp (hMsub ht)).2
  set D : Finset (Finset (Fin n)) :=
    (univ.filter fun s : Finset (Fin n) => #s < j) ∪ M with hDdef
  have hideal : IsOrderIdeal D := by
    intro s t hsD hts
    rcases Finset.mem_union.mp hsD with hsm | hsm
    · exact Finset.mem_union_left _ (mem_filter.mpr
        ⟨mem_univ t, lt_of_le_of_lt (card_le_card hts)
          (mem_filter.mp hsm).2⟩)
    · rcases lt_or_ge (#t) j with htj | htj
      · exact Finset.mem_union_left _ (mem_filter.mpr ⟨mem_univ t, htj⟩)
      · have hst : t = s := Finset.eq_of_subset_of_card_le hts
          (by rw [hMj s hsm]; exact htj)
        rw [hst]
        exact Finset.mem_union_right _ hsm
  have hbelow : ∀ i : ℕ, i < j → fEntry D i = n.choose i := by
    intro i hi
    have h : D.filter (fun t => #t = i) =
        univ.filter fun t : Finset (Fin n) => #t = i := by
      ext t
      simp only [hDdef, mem_filter, Finset.mem_union, mem_univ, true_and]
      constructor
      · rintro ⟨-, h2⟩
        exact h2
      · intro h2
        exact ⟨Or.inl (by omega), h2⟩
    rw [fEntry, h]
    exact fEntry_univ i
  have hat : fEntry D j = m := by
    have h : D.filter (fun t => #t = j) = M := by
      ext t
      simp only [hDdef, mem_filter, Finset.mem_union, mem_univ, true_and]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · omega
        · exact h1
      · intro ht
        exact ⟨Or.inr ht, hMj t ht⟩
    rw [fEntry, h, hMcard]
  have habove : ∀ i : ℕ, j < i → fEntry D i = 0 := by
    intro i hi
    rw [fEntry, card_eq_zero, filter_eq_empty_iff]
    intro t htD
    rcases Finset.mem_union.mp htD with ht | ht
    · have := (mem_filter.mp ht).2
      omega
    · have := hMj t ht
      omega
  refine ⟨fvecN D, mem_Fn.mpr ⟨D, hideal, rfl⟩, ?_, ?_, ?_⟩
  · refine top_eq_of_pos_of_zero hjn ?_ ?_
    · show 0 < fEntry D j
      omega
    · intro i hi
      show fEntry D i.val = 0
      exact habove i.val hi
  · have hle : j ≤ indeg (fvecN D) := by
      rw [le_indeg_iff (by omega)]
      intro i hi
      show n.choose i.val ≤ fEntry D i.val
      rw [hbelow i.val hi]
    have hge : indeg (fvecN D) ≤ j :=
      indeg_le_of_lt (j := ⟨j, Nat.lt_succ_of_le hjn⟩)
        (show fEntry D j < n.choose j by omega)
    omega
  · exact hat

/-- `lem-A-structure`, second claim: `A[j][j] = C(n,j) − 1`, via the
bijection `s⃗ ↦ s(j)` onto `{1, …, C(n,j) − 1}`.  Proved for **all**
`0 ≤ j ≤ n`: at `j = 0` it reads `A[0][0] = C(n,0) − 1 = 0`, which is the
manuscript's separate third claim — the printed `1 ≤ j` hypothesis is
unnecessary. -/
theorem Amat_diag (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    Amat n (j : ℤ) (j : ℤ) = n.choose j - 1 := by
  have hjlt : j < n + 1 := Nat.lt_succ_of_le hj
  rw [Amat]
  have hcard :
      #((Fn n).filter fun s => top s = (j : ℤ) ∧ (indeg s : ℤ) = (j : ℤ)) =
        #(Finset.Icc 1 (n.choose j - 1)) := by
    refine Finset.card_bij (fun s _ => s ⟨j, hjlt⟩) ?_ ?_ ?_
    · intro s hs
      obtain ⟨hsF, hstop, hsind⟩ := mem_filter.mp hs
      have h1 : 0 < s ⟨j, hjlt⟩ :=
        apply_pos_of_le_top hsF (show (j : ℤ) ≤ top s by omega)
      have h2 : s ⟨j, hjlt⟩ < n.choose j :=
        apply_lt_choose_of_indeg_le hsF (show indeg s ≤ j by omega)
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    · intro s hs t ht heq
      obtain ⟨hsF, hstop, hsind⟩ := mem_filter.mp hs
      obtain ⟨htF, httop, htind⟩ := mem_filter.mp ht
      funext i
      rcases lt_trichotomy i.val j with hij | hij | hij
      · rw [apply_eq_choose_of_lt_indeg hsF (by omega),
          apply_eq_choose_of_lt_indeg htF (by omega)]
      · have hi : i = ⟨j, hjlt⟩ := Fin.ext hij
        rw [hi]
        exact heq
      · rw [apply_eq_zero_of_top_lt (show top s < (i.val : ℤ) by omega),
          apply_eq_zero_of_top_lt (show top t < (i.val : ℤ) by omega)]
    · intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      have hchoose : 0 < n.choose j := Nat.choose_pos hj
      obtain ⟨s, hsF, hstop, hsind, hsval⟩ :=
        exists_mem_Fn_diag hj hm1 (by omega)
      exact ⟨s, mem_filter.mpr ⟨hsF, hstop, by omega⟩, hsval⟩
  rw [hcard, Nat.card_Icc]
  omega

/-- `lem-A-structure`, third claim: `A[0][0] = 0` — the `j = 0` case of
`Amat_diag`, since `C(n,0) − 1 = 0`. -/
theorem Amat_zero_zero (n : ℕ) : Amat n 0 0 = 0 := by
  have h := Amat_diag n (Nat.zero_le n)
  simpa using h

/-- `lem-A-structure`, fourth claim: row `τ = −1` vanishes away from
`ρ = 0`; together with rung A's `Amat_corner_void` (`A[−1][0] = 1`) this
is the full description of the row. -/
theorem Amat_row_void_eq_zero (n : ℕ) {ρ : ℤ} (h : ρ ≠ 0) :
    Amat n (-1) ρ = 0 := by
  rw [Amat, card_eq_zero, filter_eq_empty_iff]
  rintro s - ⟨htop, hind⟩
  rw [top_eq_neg_one_iff] at htop
  subst htop
  rw [indeg_zero] at hind
  omega

/-! ## `prop-threshold`: the saturation threshold `δ ≥ n + 1` -/

/-- Saturation above the threshold: for `δ ≥ n+1` the chaining condition
`ρ > τ − δ` is vacuous, so every row of `T(δ)` is `u⃗`: `T(δ) = 1⃗ u⃗`,
manifestly of rank one.  This is the matrix engine behind both
`prop-threshold` and `prop-perron-threshold`. -/
theorem Tmat_eq_vecMulVec_of_le {δ : ℤ} (h : (n : ℤ) + 1 ≤ δ) :
    Tmat n δ = vecMulVec (onesCol n) (uVec n) := by
  ext k k'
  have hfil : (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter
      (fun ρ => tauOf k - δ < ρ) = Finset.Icc (0 : ℤ) ((n : ℤ) + 1) := by
    refine Finset.filter_true_of_mem fun ρ hρ => ?_
    rw [Finset.mem_Icc] at hρ
    have := tauOf_le k
    omega
  rw [Tmat_apply, hfil, vecMulVec_apply]
  simp only [onesCol, uVec, one_mul]

/-- `prop-threshold`, the equivalence, proved directly on the `Finset`:
the chained locus exhausts the full Cartesian power `𝓕_n^{r+1}` **iff**
every gap is at least `n + 1`.  Stated for arbitrary (not necessarily
sorted) `d`, with the gaps as honest ℤ-differences. -/
theorem chainedTuples_eq_piFinset_iff (n r : ℕ) (d : Fin (r + 1) → ℕ) :
    chainedTuples n (r + 1) d =
        Fintype.piFinset (fun _ : Fin (r + 1) => Fn n) ↔
      ∀ i : Fin r, (n : ℤ) + 1 ≤ gaps d i := by
  constructor
  · -- only if: exhibit the excluded tuple at a small gap
    intro heq
    by_contra hgap
    obtain ⟨i, hi⟩ := not_forall.mp hgap
    have hmem : (fun j : Fin (r + 1) =>
        if j.val ≤ i.val then fullVec n else (0 : Fin (n + 1) → ℕ)) ∈
          Fintype.piFinset (fun _ : Fin (r + 1) => Fn n) := by
      rw [Fintype.mem_piFinset]
      intro j
      split_ifs
      · exact fullVec_mem_Fn
      · exact zero_mem_Fn
    rw [← heq] at hmem
    have hch := (mem_chainedTuples.mp hmem).2
    have hcon := hch (i := i.castSucc) (j := i.succ)
      (by simp [Fin.val_succ, Fin.val_castSucc])
    simp only [hatTop, hatIndeg, Fin.val_castSucc, Fin.val_succ] at hcon
    split_ifs at hcon <;>
      first
        | omega
        | · rw [top_fullVec, indeg_zero] at hcon
            simp only [gaps] at hi
            omega
  · -- if: with every gap `≥ n+1` the constraint holds for any tuple
    intro hgap
    refine Finset.Subset.antisymm (filter_subset _ _) ?_
    intro s hsmem
    refine mem_chainedTuples.mpr
      ⟨fun i => Fintype.mem_piFinset.mp hsmem i, ?_⟩
    intro a b hab
    have ha : a.val < r := by
      have := b.isLt
      omega
    have hg := hgap ⟨a.val, ha⟩
    simp only [gaps] at hg
    have hcs : (⟨a.val, ha⟩ : Fin r).castSucc = a := Fin.ext rfl
    have hsc : (⟨a.val, ha⟩ : Fin r).succ = b := Fin.ext hab
    rw [hcs, hsc] at hg
    simp only [hatTop, hatIndeg]
    have h1 := top_le (s a)
    have h2 : (0 : ℤ) ≤ (indeg (s b) : ℤ) := Int.natCast_nonneg _
    omega

/-- `prop-threshold` for cardinalities:
`#(chained tuples) = |𝓕_n|^{r+1}` iff every gap is at least `n+1`.
Cardinality equality forces set equality since the chained locus sits
inside the power. -/
theorem card_chainedTuples_eq_pow_iff (n r : ℕ) (d : Fin (r + 1) → ℕ) :
    #(chainedTuples n (r + 1) d) = #(Fn n) ^ (r + 1) ↔
      ∀ i : Fin r, (n : ℤ) + 1 ≤ gaps d i := by
  rw [← chainedTuples_eq_piFinset_iff]
  have hcard : #(Fintype.piFinset (fun _ : Fin (r + 1) => Fn n)) =
      #(Fn n) ^ (r + 1) := by
    rw [Fintype.card_piFinset]
    simp
  constructor
  · intro h
    exact Finset.eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  · intro h
    rw [h, hcard]

/-- `prop-threshold` as printed (`|FF(d⃗)| = |𝓕_n|^{r+1}` iff all gaps
`≥ n+1`), modulo the same explicit surjectivity hypothesis as C2b's
`card_ffSetN` — the open half of `thm-chaining`, deliberately not
formalised (rung C3 is a non-target). -/
theorem ncard_ffSetN_eq_pow_iff (n r : ℕ) (d : Fin (r + 1) → ℕ)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ Fn n) ∧ Chained d s}
      (ffSetN n d)) :
    (ffSetN n d).ncard = #(Fn n) ^ (r + 1) ↔
      ∀ i : Fin r, (n : ℤ) + 1 ≤ gaps d i := by
  rw [card_ffSetN n r d hsurj, ← card_chainedTuples]
  exact card_chainedTuples_eq_pow_iff n r d

/-- `prop-threshold`, sharpness clause: at gap `δ = n` the chaining
constraint `tp(s⃗) < indeg(t⃗) + δ` fails for **exactly one** pair of
members of `𝓕_n`, namely `(full simplex, void family)`. -/
theorem filter_not_chained_at_n (n : ℕ) :
    (((Fn n) ×ˢ (Fn n)).filter fun p =>
        ¬ top p.1 < (indeg p.2 : ℤ) + n) =
      {(fullVec n, (0 : Fin (n + 1) → ℕ))} := by
  ext p
  simp only [mem_filter, Finset.mem_product, mem_singleton, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, hle⟩
    have ht := top_le p.1
    have hi := Int.natCast_nonneg (indeg p.2)
    have htop : top p.1 = (n : ℤ) := by omega
    have hind : indeg p.2 = 0 := by omega
    exact Prod.ext_iff.mpr
      ⟨eq_fullVec_of_top_eq_n h1 htop, eq_zero_of_indeg_eq_zero h2 hind⟩
  · rintro rfl
    refine ⟨⟨fullVec_mem_Fn, zero_mem_Fn⟩, ?_⟩
    show (indeg (0 : Fin (n + 1) → ℕ) : ℤ) + n ≤ top (fullVec n)
    rw [indeg_zero, top_fullVec]
    omega

/-- The saturated bilinear form absorbs one factor:
`w⃗ (1⃗ u⃗) 1⃗ = (w⃗ · 1⃗) |𝓕_n|`. -/
theorem vecMul_saturated_dot (w : Fin (n + 2) → ℕ) :
    w ᵥ* vecMulVec (onesCol n) (uVec n) ⬝ᵥ onesCol n =
      (w ⬝ᵥ onesCol n) * #(Fn n) := by
  have hrow : ∀ k', (w ᵥ* vecMulVec (onesCol n) (uVec n)) k' =
      (w ⬝ᵥ onesCol n) * uVec n k' := by
    intro k'
    simp only [Matrix.vecMul, dotProduct, vecMulVec_apply, onesCol,
      mul_one, one_mul, Finset.sum_mul]
  rw [dotProduct_onesCol]
  calc ∑ k', (w ᵥ* vecMulVec (onesCol n) (uVec n)) k'
      = ∑ k', (w ⬝ᵥ onesCol n) * uVec n k' :=
        Finset.sum_congr rfl fun k' _ => hrow k'
    _ = (w ⬝ᵥ onesCol n) * ∑ k', uVec n k' := by
        rw [Finset.mul_sum]
    _ = (w ⬝ᵥ onesCol n) * #(Fn n) := by rw [sum_uVec]

/-- `prop-threshold`, matrix side: with every gap `≥ n+1` the transfer
product collapses, `u⃗ T(δ₁)⋯T(δ_r) 1⃗ = |𝓕_n|^{r+1}` — the rank-one
factor absorbs one power of `|𝓕_n|` per step. -/
theorem vecMul_Tprod_dot_of_saturated (n r : ℕ) {g : Fin r → ℤ}
    (hg : ∀ i, (n : ℤ) + 1 ≤ g i) :
    uVec n ᵥ* Tprod n r g ⬝ᵥ onesCol n = #(Fn n) ^ (r + 1) := by
  induction r with
  | zero =>
    rw [Tprod_zero, Matrix.vecMul_one, dotProduct_onesCol, sum_uVec,
      pow_one]
  | succ r ih =>
    rw [Tprod_succ, ← Matrix.vecMul_vecMul,
      Tmat_eq_vecMulVec_of_le (hg (Fin.last r)), vecMul_saturated_dot,
      ih (g := g ∘ Fin.castSucc) (fun i => hg i.castSucc), ← pow_succ]

/-! ## `prop-normalform`: `T(δ) = P^δ B` -/

/-- The saturating one-step shift `P` of `prop-normalform`:
`P[τ][τ'] = 1` iff `τ' = max(τ − 1, −1)`, and `0` otherwise.  In the
`Fin (n+2)` indexing (`tauOf k = k − 1`) the clamped decrement on `τ` is
truncated ℕ-subtraction on the index, `k' = k − 1` — the clamp at
`τ = −1` is exactly the clamp of `Nat.sub` at `0`. -/
def Pmat (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℕ :=
  Matrix.of fun k k' => if k'.val = k.val - 1 then 1 else 0

/-- The dictionary to the printed description of `P`: the entry is `1`
exactly when `tauOf k' = max (tauOf k − 1) (−1)`. -/
theorem Pmat_apply_eq_one_iff {k k' : Fin (n + 2)} :
    Pmat n k k' = 1 ↔ tauOf k' = max (tauOf k - 1) (-1) := by
  simp only [Pmat, Matrix.of_apply, tauOf]
  split_ifs with h
  · exact iff_of_true rfl (by omega)
  · rw [false_iff]
    intro hc
    refine h ?_
    rcases lt_or_ge ((k.val : ℤ) - 1 - 1) (-1) with hm | hm
    · rw [max_eq_right hm.le] at hc
      omega
    · rw [max_eq_left hm] at hc
      omega

/-- `P^δ` is the `δ`-step clamped shift: index `k` goes to `k − δ`
(truncated), i.e. `τ` goes to `max(τ − δ, −1)`. -/
theorem Pmat_pow_apply (n : ℕ) (δ : ℕ) (k k' : Fin (n + 2)) :
    (Pmat n ^ δ) k k' = if k'.val = k.val - δ then 1 else 0 := by
  induction δ generalizing k' with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    have hiff : (k = k') ↔ (k'.val = k.val - 0) := by
      rw [Nat.sub_zero]
      exact ⟨fun h => h ▸ rfl, fun h => Fin.ext h.symm⟩
    simp only [hiff]
  | succ δ ih =>
    rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_eq_single (⟨k.val - δ, by omega⟩ : Fin (n + 2))]
    · rw [ih, ite_eq_left rfl, one_mul]
      show (if k'.val = k.val - δ - 1 then 1 else 0) =
        if k'.val = k.val - (δ + 1) then 1 else 0
      rw [Nat.sub_sub]
    · intro j _ hj
      rw [ih, ite_eq_right (fun h => hj (Fin.ext h)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The clamp, entrywise: row `k` of `T(δ)` is row `k − δ` (truncated) of
`T(0)` — `T(δ)[τ][·] = T(0)[max(τ−δ, −1)][·]`, both the `τ − δ ≥ −1`
case and the saturated case in one truncated subtraction. -/
theorem Tmat_row_shift (n : ℕ) (δ : ℕ) (k : Fin (n + 2)) :
    Tmat n (δ : ℤ) k = Tmat n 0 ⟨k.val - δ, by omega⟩ := by
  funext k'
  rw [Tmat_apply, Tmat_apply]
  refine Finset.sum_congr (Finset.filter_congr fun ρ hρ => ?_)
    fun ρ _ => rfl
  rw [Finset.mem_Icc] at hρ
  show tauOf k - (δ : ℤ) < ρ ↔
    tauOf (⟨k.val - δ, by omega⟩ : Fin (n + 2)) - 0 < ρ
  show ((k.val : ℤ) - 1) - (δ : ℤ) < ρ ↔
    (((k.val - δ : ℕ) : ℤ) - 1) - 0 < ρ
  omega

/-- `prop-normalform`, first identity: `T(δ) = P^δ B` with `B = T(0)`,
for every `δ : ℕ` (the printed `δ ≥ 0`). -/
theorem Tmat_eq_Pmat_pow_mul (n : ℕ) (δ : ℕ) :
    Tmat n (δ : ℤ) = Pmat n ^ δ * Tmat n 0 := by
  ext k k'
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨k.val - δ, by omega⟩ : Fin (n + 2))]
  · rw [Pmat_pow_apply, ite_eq_left rfl, one_mul]
    exact congrFun (Tmat_row_shift n δ k) k'
  · intro j _ hj
    rw [Pmat_pow_apply, ite_eq_right (fun h => hj (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `prop-normalform`, second identity, row form: `u⃗` is row `−1`
(index `0`) of `B = T(0)` — the condition `ρ > −1` defining row `−1` is
vacuous over `ρ ≥ 0`. -/
theorem uVec_eq_Tmat_zero_row (n : ℕ) : uVec n = Tmat n 0 0 := by
  funext k'
  have hfil : (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)).filter
      (fun ρ => tauOf (0 : Fin (n + 2)) - 0 < ρ) =
        Finset.Icc (0 : ℤ) ((n : ℤ) + 1) := by
    refine Finset.filter_true_of_mem fun ρ hρ => ?_
    rw [Finset.mem_Icc] at hρ
    simp only [tauOf, Fin.val_zero]
    omega
  rw [Tmat_apply, hfil]
  simp only [uVec]

/-- `prop-normalform`, second identity, matrix form:
`u⃗ = e_{−1}ᵀ B`, with `e_{−1}` the standard basis vector at the void
index. -/
theorem uVec_eq_single_vecMul (n : ℕ) :
    uVec n = Pi.single (0 : Fin (n + 2)) 1 ᵥ* Tmat n 0 := by
  funext k'
  rw [uVec_eq_Tmat_zero_row]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- The fully factored product `(P^{g 0} B) ⋯ (P^{g (r−1)} B)` of
`eq:normalform`, by the same right-peeling recursion as `Tprod`. -/
def PBprod (n : ℕ) : (r : ℕ) → (Fin r → ℕ) →
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℕ
  | 0, _ => 1
  | r + 1, g => PBprod n r (g ∘ Fin.castSucc) *
      (Pmat n ^ g (Fin.last r) * Tmat n 0)

@[simp] theorem PBprod_zero (n : ℕ) (g : Fin 0 → ℕ) :
    PBprod n 0 g = 1 := rfl

@[simp] theorem PBprod_succ (n r : ℕ) (g : Fin (r + 1) → ℕ) :
    PBprod n (r + 1) g = PBprod n r (g ∘ Fin.castSucc) *
      (Pmat n ^ g (Fin.last r) * Tmat n 0) := rfl

/-- For ℕ-gaps the transfer product *is* the fully factored product. -/
theorem Tprod_eq_PBprod (n : ℕ) : ∀ (r : ℕ) (g : Fin r → ℕ),
    Tprod n r (fun i => (g i : ℤ)) = PBprod n r g := by
  intro r
  induction r with
  | zero => intro g; rfl
  | succ r ih =>
    intro g
    show Tprod n r ((fun i => (g i : ℤ)) ∘ Fin.castSucc) *
        Tmat n (g (Fin.last r) : ℤ) = _
    rw [show (fun i => (g i : ℤ)) ∘ Fin.castSucc =
          fun i => ((g ∘ Fin.castSucc) i : ℤ) from rfl,
      ih (g ∘ Fin.castSucc), Tmat_eq_Pmat_pow_mul, PBprod_succ]

/-- `eq:normalform`, the fully factored count: for sorted `d⃗` the
chained count is `e_{−1}ᵀ B (P^{δ₁} B) ⋯ (P^{δ_r} B) 1⃗` — all the gap
dependence sits in the powers of the single `0/1` shift `P`. -/
theorem card_chainedTuples_normalform (n r : ℕ) {d : Fin (r + 1) → ℕ}
    (hd : Monotone d) :
    #(chainedTuples n (r + 1) d) =
      Pi.single (0 : Fin (n + 2)) 1 ᵥ*
        (Tmat n 0 * PBprod n r fun i => d i.succ - d i.castSucc) ⬝ᵥ
        onesCol n := by
  rw [card_chainedTuples, gaps_eq_of_monotone hd,
    Tprod_eq_PBprod n r (fun i => d i.succ - d i.castSucc),
    uVec_eq_single_vecMul, Matrix.vecMul_vecMul]

/-- `eq:normalform`, third equation as printed:
`|FF(d⃗)| = e_{−1}ᵀ B P^{δ₂} B ⋯ P^{δ_r} B 1⃗` for sorted `d⃗`, modulo the
same surjectivity hypothesis as C2b (`thm-chaining`'s open half). -/
theorem ncard_ffSetN_normalform (n r : ℕ) {d : Fin (r + 1) → ℕ}
    (hd : Monotone d)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ Fn n) ∧ Chained d s}
      (ffSetN n d)) :
    (ffSetN n d).ncard =
      Pi.single (0 : Fin (n + 2)) 1 ᵥ*
        (Tmat n 0 * PBprod n r fun i => d i.succ - d i.castSucc) ⬝ᵥ
        onesCol n := by
  rw [card_ffSetN n r d hsurj, ← card_chainedTuples,
    card_chainedTuples_normalform n r hd]

/-! ## Rung D4: `prop-perron-threshold`, improper half, as an eigenvalue
statement

**Scope note (deliberate, per the plan's decision of 2026-09-17).**  What
is formalised is the *eigenvalue restatement* of the improper half: above
the threshold `δ ≥ n+1` the matrix `T(δ)` is rank one
(`Tmat_eq_vecMulVec_of_le`), it has `1⃗` as an eigenvector with
eigenvalue `|𝓕_n|` (`Tmat_mulVec_onesCol_of_le`), and over ℚ every
eigenvalue with a non-zero eigenvector is `0` or `|𝓕_n|`
(`eigenvalue_eq_zero_or_card`).  **What is *not* formalised is the word
"Perron"**: that `|𝓕_n|` is the eigenvalue of largest modulus, with a
non-negative eigenvector — true, but requiring the Perron–Frobenius
theory (and a spectral radius) that Mathlib currently lacks.  The printed
proposition's "Perron root" wording is therefore not certified as
printed; in the rank-one case the loss is only the comparison of
`|𝓕_n|` against `0`.  The proper half (`λ_pr`, threshold `δ ≥ n−1`) is
rung D3 and is not attempted here. -/

/-- D4, the eigenvector: above the threshold `1⃗` is an eigenvector of
`T(δ)` with eigenvalue `|𝓕_n|` — over ℕ already. -/
theorem Tmat_mulVec_onesCol_of_le {δ : ℤ} (h : (n : ℤ) + 1 ≤ δ) :
    Tmat n δ *ᵥ onesCol n = #(Fn n) • onesCol n := by
  funext k
  rw [Tmat_eq_vecMulVec_of_le h]
  have hl : (vecMulVec (onesCol n) (uVec n) *ᵥ onesCol n) k =
      ∑ j, uVec n j := by
    simp [Matrix.mulVec, dotProduct, vecMulVec_apply, onesCol]
  rw [hl, sum_uVec]
  simp [onesCol]

/-- The ℚ-cast of the saturated matrix: still `1⃗ u⃗`. -/
theorem Tmat_map_ratCast_of_le {δ : ℤ} (h : (n : ℤ) + 1 ≤ δ) :
    (Tmat n δ).map (Nat.cast : ℕ → ℚ) =
      vecMulVec (fun _ => 1) (fun k => (uVec n k : ℚ)) := by
  rw [Tmat_eq_vecMulVec_of_le h]
  ext k k'
  simp [Matrix.map_apply, vecMulVec_apply, onesCol]

/-- D4, the "only non-zero eigenvalue" content: over ℚ, any eigenvalue
of the saturated transfer matrix with a non-zero eigenvector is `0` or
`|𝓕_n|`.  (The rank-one factorisation forces every eigenvector with
non-zero eigenvalue to be constant.) -/
theorem eigenvalue_eq_zero_or_card {δ : ℤ} (h : (n : ℤ) + 1 ≤ δ)
    {μ : ℚ} {v : Fin (n + 2) → ℚ} (hv : v ≠ 0)
    (heig : (Tmat n δ).map (Nat.cast : ℕ → ℚ) *ᵥ v = μ • v) :
    μ = 0 ∨ μ = (#(Fn n) : ℚ) := by
  by_cases hμ : μ = 0
  · exact Or.inl hμ
  · right
    rw [Tmat_map_ratCast_of_le h] at heig
    set c : ℚ := (fun k => (uVec n k : ℚ)) ⬝ᵥ v with hc
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
    have hsum : c = (c / μ) * (#(Fn n) : ℚ) := by
      calc c = ∑ k, (uVec n k : ℚ) * v k := by rw [hc, dotProduct]
        _ = ∑ k, (uVec n k : ℚ) * (c / μ) :=
            Finset.sum_congr rfl fun k _ => by rw [hvk k]
        _ = (∑ k, (uVec n k : ℚ)) * (c / μ) := by
            rw [Finset.sum_mul]
        _ = (#(Fn n) : ℚ) * (c / μ) := by
            rw [← Nat.cast_sum, sum_uVec]
        _ = (c / μ) * (#(Fn n) : ℚ) := mul_comm _ _
    field_simp at hsum
    linarith [hsum]

end ExteriorConvex
