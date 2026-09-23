/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D2 of the article-2 formalisation: the exact degree at `δ = 0`, improper half

Formalisation of `prop-delta0` and the **improper half** of
`thm-delta0-degrees` from `article/exterior-convex_article2_draft_3.org`,
following the proof written in
`working-notes/delta0-exact-degrees-proof.org` (Lemma A is rung D1's
`Amat_superdiag`/`Amat_diag`; the Reduction and the Corner evaluation are
consumed here), per `working-notes/PLAN-formalise-article2.org` (rung D2).

**Refactored 2026-09-18** (the plan's "do the refactor first", ahead of
rung D3): the Reduction and the Corner evaluation, which the working note
states for an *arbitrary* matrix and arbitrary vectors, now live in that
generality in `Counting/NilpotentReduction.lean`; this file re-derives
its concrete `Nmat`-versions from them (`Nmat_pow_apply_eq_zero`,
`Nmat_pow_staircase`, `Nmat_pow_eq_zero`, and the binomial expansion in
`cast_card_chainedTuples_of_gaps_eq_zero`).  **No theorem statement in
this file changed** — the statements below are the rung-D2 ones cited in
the manuscript's §10.1, only their proofs now route through the general
lemmas.

Contents, by manuscript item:

* **`prop-delta0`** — `Tmat_zero_eq_zero_of_lt` and
  `Tmat_zero_blockTriangular` (`T(0)` is upper triangular in the
  `tp`-ordering), `Tmat_zero_diag` (`T(0)[τ][τ] = 1`), and
  `isNilpotent_Nmat`/`Nmat_pow_eq_zero` (`N = T(0) − I` is nilpotent over
  ℚ, `N^{n+2} = 0` — unipotence of `T(0)`).  The degree *bound* `≤ n+1`
  of `prop-delta0` is subsumed by the exact-degree theorem below.
* **`eq:delta0-superdiag`** — `Tmat_zero_superdiag`
  (`T(0)[τ][τ+1] = C(n, τ+1)`: Pascal's row `n` on the superdiagonal, via
  D1's `Amat_diag` + `Amat_superdiag`).
* **`thm-delta0-degrees`, improper half.**  Design decision (per the
  plan): everything is cast into ℚ **once**, at `Nmat := T(0).map ℕ→ℚ − 1`
  — `Tmat` is ℕ-valued and `T(0) − I` cannot live over ℕ.  A second reason, sharper because
    it fails silently: `/` is total in Lean and ℕ-division *floors*, so a
    leading coefficient computed over ℕ would give `cpBracket 3 2 / 2! = 1`
    instead of `3/2` — a wrong value that still typechecks and still builds.
    (Division by zero is harmless here by `div_zero`, every denominator being
    a factorial; the flooring is the trap.)  Then:
  - *(a) the certified core*, the brackets `cBracket n k = u⃗ N^k 1⃗`:
    `cBracket_eq_zero_of_ge` (`= 0` for `k ≥ n+2`),
    `cBracket_top` (`u⃗ N^{n+1} 1⃗ = ∏_{j=0}^n C(n,j)`, by the corner
    evaluation `Nmat_pow_staircase` — only the full staircase survives)
    with `cBracket_top_pos`, and the binomial expansion
    `cast_card_chainedTuples_of_gaps_eq_zero`
    (`count = ∑_k C(r,k)·cₖ` for `r` gaps, all zero — `eq:delta0-expansion`
    with the manuscript's `r − 1` summation variable equal to the gap
    count).
  - *(b) the polynomial*, `delta0Poly n : Polynomial ℚ`, built explicitly
    as `∑_k C(cₖ/k!)·(descPochhammer ℚ k).comp (X − 1)` so that its value
    at `r` is `∑_k C(r−1,k)·cₖ`: `delta0Poly_eval_natCast`,
    `delta0Poly_natDegree` (degree **exactly** `n+1`),
    `delta0Poly_leadingCoeff` (`(∏_{j=0}^n C(n,j))/(n+1)!`), and the
    bundled headline `thm_delta0_degrees_improper`, with the `|FF|` form
    `cast_ncard_ffSetN_zero_eval` carrying C2b's explicit surjectivity
    hypothesis, as it must.

A finding of the formalisation: **no lower bound on `n` is needed** — the
printed theorem says `n ≥ 1`, but every statement here, including exact
degree `n+1` and the leading coefficient, is proved for all `n : ℕ`
(at `n = 0` it reads: degree exactly `1`, leading coefficient `1/1! = 1`).
Also `u⃗[−1] = 1` (`uVec_zero`, the void family alone) is used exactly
once, in the corner evaluation `cBracket_top` — nowhere else.

**Out of scope, deliberately** (rung D3): the proper half of
`thm-delta0-degrees` (`A′`, `u⃗′`, `T′(0)`, the invariant-block repair) and
`prop-proper-threshold`.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`); the sanity checks — at `n = 2` the brackets
`(c₀,…,c₃) = (5, 9, 7, 2)` and the counts `14, 30, 55, 91` at
`1, 2, 3, 4` gaps; at `n = 3` the bracket `c₄ = 9 = 1·3·3·1` and the
count `43` at one gap — were `#eval`s during development and stay out of
the formal statements, deliberately.
-/
import ExteriorConvex.Counting.Structure
import ExteriorConvex.Counting.NilpotentReduction

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## `prop-delta0`: `T(0)` is unipotent

Row `k` of `T(0)` sums the rows of `A` over `ρ > tauOf k`; combined with
`A`'s support bound `ρ ≤ τ' + 1` this gives upper triangularity, and on
the diagonal only `ρ = τ + 1` survives, whose `A`-entry is `1` by D1's
superdiagonal rigidity. -/

/-- Row `k` of `T(0)`: the `ρ`-range `{0, …, n+1} ∩ {ρ > τ}` is
`{k, …, n+1}` in the `Fin (n+2)` indexing (`τ = k − 1`). -/
theorem Tmat_zero_apply_eq_sum (k k' : Fin (n + 2)) :
    Tmat n 0 k k' =
      ∑ ρ ∈ Finset.Icc (k.val : ℤ) ((n : ℤ) + 1), Amat n (tauOf k') ρ := by
  rw [Tmat_apply]
  congr 1
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_Icc, tauOf, sub_zero]
  omega

/-- `prop-delta0`, triangularity: `T(0)[τ][τ'] = 0` for `τ' < τ` — a
non-zero entry needs `τ + 1 ≤ ρ ≤ τ' + 1`. -/
theorem Tmat_zero_eq_zero_of_lt {k k' : Fin (n + 2)} (h : k' < k) :
    Tmat n 0 k k' = 0 := by
  rw [Tmat_zero_apply_eq_sum]
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  rw [Finset.mem_Icc] at hρ
  refine Amat_eq_zero_of_add_one_lt ?_
  have hlt : k'.val < k.val := h
  simp only [tauOf]
  omega

/-- `prop-delta0`, triangularity in Mathlib's vocabulary: `T(0)` is
`BlockTriangular` for the identity ordering. -/
theorem Tmat_zero_blockTriangular (n : ℕ) :
    (Tmat n 0).BlockTriangular (fun k => k) :=
  fun _i _j h => Tmat_zero_eq_zero_of_lt h

/-- `prop-delta0`, unit diagonal: `T(0)[τ][τ] = A[τ][τ+1] = 1` — on the
diagonal only `ρ = τ + 1` survives, and its class is the singleton full
truncation (D1's `Amat_superdiag`; at `τ = −1` rung A's
`Amat_corner_void`). -/
theorem Tmat_zero_diag (k : Fin (n + 2)) : Tmat n 0 k k = 1 := by
  rw [Tmat_zero_apply_eq_sum]
  rw [Finset.sum_eq_single_of_mem (k.val : ℤ)
      (Finset.mem_Icc.mpr ⟨le_refl _, by have := k.isLt; omega⟩)
      (fun ρ hρ hne => Amat_eq_zero_of_add_one_lt (by
        rw [Finset.mem_Icc] at hρ
        simp only [tauOf]
        omega))]
  rcases Nat.eq_zero_or_pos k.val with h0 | hpos
  · have hτ : tauOf k = -1 := by simp only [tauOf]; omega
    rw [hτ, h0]
    simpa using Amat_corner_void n
  · obtain ⟨j, hj⟩ : ∃ j, k.val = j + 1 := ⟨k.val - 1, by omega⟩
    have hjn : j ≤ n := by have := k.isLt; omega
    have h1 : tauOf k = (j : ℤ) := by simp only [tauOf]; omega
    have h2 : (k.val : ℤ) = (j : ℤ) + 1 := by omega
    rw [h1, h2]
    exact Amat_superdiag n hjn

/-- `eq:delta0-superdiag`: `T(0)[τ][τ+1] = A[τ+1][τ+1] + A[τ+1][τ+2] =
(C(n,τ+1) − 1) + 1 = C(n, τ+1)` — Pascal's row `n`, by D1's diagonal and
superdiagonal of `A`.  In the `Fin (n+2)` indexing the row is `j = τ + 1`,
so the entry reads `C(n, j)` at position `(j, j+1)`. -/
theorem Tmat_zero_superdiag {j : ℕ} (hj : j ≤ n) :
    Tmat n 0 ⟨j, by omega⟩ ⟨j + 1, by omega⟩ = n.choose j := by
  rw [Tmat_zero_apply_eq_sum]
  have hτ : tauOf (⟨j + 1, by omega⟩ : Fin (n + 2)) = (j : ℤ) := by
    simp only [tauOf]
    omega
  have hval : ((⟨j, by omega⟩ : Fin (n + 2)).val : ℤ) = (j : ℤ) := rfl
  rw [hτ, hval]
  have hsub : ({(j : ℤ), (j : ℤ) + 1} : Finset ℤ) ⊆
      Finset.Icc (j : ℤ) ((n : ℤ) + 1) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    rw [Finset.mem_Icc]
    rcases hρ with rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub (fun ρ hρ hρ' => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ'
    rw [Finset.mem_Icc] at hρ
    exact Amat_eq_zero_of_add_one_lt (by omega))]
  rw [Finset.sum_pair (by omega : (j : ℤ) ≠ (j : ℤ) + 1)]
  rw [Amat_diag n hj, Amat_superdiag n hj]
  have := Nat.choose_pos hj
  omega

/-! ## The nilpotent part `N = T(0) − I`, over ℚ

Design decision (per the plan): cast once, here.  `Tmat` is ℕ-valued and
truncated subtraction would silently give the wrong matrix, so `N` is
defined over ℚ, where the leading coefficient lives anyway. -/

/-- `N = T(0) − I` over ℚ: the strictly-upper-triangular part of the
unipotent `T(0)`. -/
def Nmat (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  (Tmat n 0).map (Nat.cast : ℕ → ℚ) - 1

/-- The ℚ-cast of `T(0)` is `I + N`. -/
theorem map_Tmat_zero_eq (n : ℕ) :
    (Tmat n 0).map (Nat.cast : ℕ → ℚ) = Nmat n + 1 := by
  rw [Nmat]
  abel

/-- `N` is strictly upper triangular: entries on and below the diagonal
vanish. -/
theorem Nmat_apply_eq_zero_of_le {i j : Fin (n + 2)} (h : j ≤ i) :
    Nmat n i j = 0 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · simp [Nmat, Matrix.sub_apply, Matrix.map_apply, Tmat_zero_diag,
      Matrix.one_apply_eq]
  · have hne : i ≠ j := (ne_of_lt hlt).symm
    simp [Nmat, Matrix.sub_apply, Matrix.map_apply,
      Tmat_zero_eq_zero_of_lt hlt, Matrix.one_apply_ne hne]

/-- The superdiagonal of `N` is the superdiagonal of `T(0)`: Pascal's
row `n`. -/
theorem Nmat_superdiag {j : ℕ} (hj : j ≤ n) :
    Nmat n ⟨j, by omega⟩ ⟨j + 1, by omega⟩ = (n.choose j : ℚ) := by
  have hne : (⟨j, by omega⟩ : Fin (n + 2)) ≠ ⟨j + 1, by omega⟩ := by
    intro hcon
    have hval := congrArg Fin.val hcon
    simp only at hval
    omega
  simp [Nmat, Matrix.sub_apply, Matrix.map_apply, Tmat_zero_superdiag hj,
    Matrix.one_apply_ne hne]

/-- `N` is strictly upper triangular, in the unbundled `val`-form the
general lemmas of `NilpotentReduction.lean` consume. -/
theorem Nmat_strictUpper (n : ℕ) :
    ∀ i j : Fin (n + 2), j.val ≤ i.val → Nmat n i j = 0 :=
  fun _i _j h => Nmat_apply_eq_zero_of_le (Fin.le_def.mpr h)

/-- Powers of `N` climb: `N^k` vanishes below the `k`-th superdiagonal.
(The general `pow_apply_eq_zero_of_strictUpper`, at `N = Nmat n`.) -/
theorem Nmat_pow_apply_eq_zero :
    ∀ (k : ℕ) {i j : Fin (n + 2)}, j.val < i.val + k →
      (Nmat n ^ k) i j = 0 :=
  pow_apply_eq_zero_of_strictUpper (Nmat_strictUpper n)

/-- `prop-delta0`, unipotence: `N^{n+2} = 0` — the strictly upper
triangular part of an `(n+2) × (n+2)` matrix is nilpotent. -/
theorem Nmat_pow_eq_zero (n : ℕ) : Nmat n ^ (n + 2) = 0 :=
  pow_eq_zero_of_strictUpper (Nmat_strictUpper n)

/-- `prop-delta0`, packaged: `T(0) − I` is nilpotent over ℚ, i.e. `T(0)`
is unipotent. -/
theorem isNilpotent_Nmat (n : ℕ) : IsNilpotent (Nmat n) :=
  ⟨n + 2, Nmat_pow_eq_zero n⟩

/-- **The corner evaluation** (the one informally-written step of the
working note, "only the full staircase does that", proved): on the exact
`k`-th superdiagonal, `N^k[i][i+k]` is the product of the superdiagonal
entries along the staircase.  (The general
`pow_apply_staircase_of_strictUpper`, at `N = Nmat n` with superdiagonal
function `g = C(n, ·)`.) -/
theorem Nmat_pow_staircase :
    ∀ (k : ℕ) {i j : Fin (n + 2)}, j.val = i.val + k →
      (Nmat n ^ k) i j = ∏ a ∈ Finset.range k, (n.choose (i.val + a) : ℚ) :=
  pow_apply_staircase_of_strictUpper (Nmat_strictUpper n)
    (fun a _h1 h2 => Nmat_superdiag (by omega))

/-! ## The brackets `cₖ = u⃗ N^k 1⃗` — deliverable (a), the certified core -/

/-- The initial vector over ℚ. -/
def uQ (n : ℕ) : Fin (n + 2) → ℚ := fun k => (uVec n k : ℚ)

/-- `u⃗[−1] = 1`: the void family is the unique member of `𝓕_n` with
`tp = −1`. -/
theorem uVec_zero (n : ℕ) : uVec n 0 = 1 := by
  rw [uVec_eq_card]
  have hτ : tauOf (0 : Fin (n + 2)) = -1 := by
    simp only [tauOf, Fin.val_zero]
    omega
  have h : (Fn n).filter (fun s => top s = tauOf (0 : Fin (n + 2))) =
      {(0 : Fin (n + 1) → ℕ)} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton, hτ]
    constructor
    · rintro ⟨-, htop⟩
      exact top_eq_neg_one_iff.mp htop
    · rintro rfl
      exact ⟨zero_mem_Fn, top_zero⟩
  rw [h, Finset.card_singleton]

/-- The brackets of `eq:delta0-expansion`: `cₖ = u⃗ N^k 1⃗`, over ℚ. -/
def cBracket (n k : ℕ) : ℚ :=
  uQ n ᵥ* Nmat n ^ k ⬝ᵥ (fun _ => (1 : ℚ))

/-- Deliverable (a), vanishing: `cₖ = 0` for `k ≥ n + 2`. -/
theorem cBracket_eq_zero_of_ge {k : ℕ} (h : n + 2 ≤ k) : cBracket n k = 0 := by
  rw [cBracket, pow_eq_zero_of_le h (Nmat_pow_eq_zero n),
    Matrix.vecMul_zero, zero_dotProduct]

/-- Deliverable (a), the top bracket: `c_{n+1} = u⃗ N^{n+1} 1⃗ =
∏_{j=0}^{n} C(n,j)` — the corner evaluation.  The only surviving entry of
`N^{n+1}` is the corner `(−1, n)`, its value is the staircase product,
and `u⃗[−1] = 1` (the **only** use of `uVec_zero` in this file). -/
theorem cBracket_top (n : ℕ) :
    cBracket n (n + 1) = ∏ j ∈ Finset.range (n + 1), (n.choose j : ℚ) := by
  rw [cBracket, dotProduct]
  have hlast : (Fin.last (n + 1)).val = n + 1 := rfl
  rw [Finset.sum_eq_single_of_mem (Fin.last (n + 1)) (Finset.mem_univ _)
      (fun j _ hne => by
    have hjv : j.val ≠ n + 1 := fun hc => hne (Fin.ext (by omega))
    have hj := j.isLt
    have hz : (uQ n ᵥ* Nmat n ^ (n + 1)) j = 0 := by
      simp only [Matrix.vecMul, dotProduct]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Nmat_pow_apply_eq_zero (n + 1) (by omega), mul_zero]
    rw [hz, zero_mul])]
  simp only [Matrix.vecMul, dotProduct, mul_one]
  rw [Finset.sum_eq_single_of_mem (0 : Fin (n + 2)) (Finset.mem_univ _)
      (fun i _ hne => by
    have hiv : i.val ≠ 0 := fun hc => hne (Fin.ext hc)
    rw [Nmat_pow_apply_eq_zero (n + 1) (by rw [hlast]; omega), mul_zero])]
  rw [Nmat_pow_staircase (n + 1) (by rw [hlast, Fin.val_zero]; omega)]
  rw [show uQ n 0 = 1 from by rw [uQ, uVec_zero, Nat.cast_one], one_mul]
  exact Finset.prod_congr rfl fun a _ => by rw [Fin.val_zero, zero_add]

/-- The top bracket is positive — every factor is a positive binomial
coefficient.  This is what makes the degree *exactly* `n + 1`. -/
theorem cBracket_top_pos (n : ℕ) : 0 < cBracket n (n + 1) := by
  rw [cBracket_top]
  refine Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_range] at hj
  exact_mod_cast Nat.choose_pos (by omega)

/-! ## The expansion `count = ∑ₖ C(r,k) cₖ` — deliverable (a), third part

`eq:delta0-expansion`: with all gaps zero the transfer product is
`T(0)^r`, and the binomial theorem for the commuting pair `(N, I)` turns
`u⃗ (I+N)^r 1⃗` into `∑ₖ C(r,k) cₖ`.  Here `r` is the **gap count** — the
manuscript's rank is `r + 1`, so this is the printed
`∑ₖ C(rank − 1, k) cₖ`. -/

/-- With every gap zero the transfer product collapses to a power. -/
theorem Tprod_zero_gaps (n : ℕ) :
    ∀ r : ℕ, Tprod n r (fun _ => (0 : ℤ)) = Tmat n 0 ^ r := by
  intro r
  induction r with
  | zero => rw [Tprod_zero, pow_zero]
  | succ r ih =>
    show Tprod n r (fun _ => (0 : ℤ)) * Tmat n 0 = Tmat n 0 ^ (r + 1)
    rw [ih, pow_succ]

/-- Casting the ℕ-valued sandwich `u⃗ T(0)^r 1⃗` into ℚ. -/
theorem cast_vecMul_pow_dot (n r : ℕ) :
    ((uVec n ᵥ* (Tmat n 0 ^ r) ⬝ᵥ onesCol n : ℕ) : ℚ) =
      uQ n ᵥ* ((Tmat n 0).map (Nat.cast : ℕ → ℚ)) ^ r ⬝ᵥ
        (fun _ => (1 : ℚ)) := by
  have hmp : ((Tmat n 0).map (Nat.cast : ℕ → ℚ)) ^ r =
      (Tmat n 0 ^ r).map (Nat.cast : ℕ → ℚ) := by
    rw [show (Nat.cast : ℕ → ℚ) = ⇑(Nat.castRingHom ℚ) from rfl,
      Matrix.map_pow]
  rw [hmp]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, uQ, onesCol,
    mul_one]
  push_cast
  rfl

/-- The binomial expansion of a single sandwich term.  (The general
`vecMul_pow_natCast_mul_dotProduct`, at the D2 sandwich.) -/
theorem vecMul_pow_natCast_dot (n m c : ℕ) :
    uQ n ᵥ* (Nmat n ^ m * (c : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ)) ⬝ᵥ
        (fun _ => (1 : ℚ)) = (c : ℚ) * cBracket n m :=
  vecMul_pow_natCast_mul_dotProduct (Nmat n) (uQ n) (fun _ => (1 : ℚ)) m c

/-- Truncation/extension of the expansion range: below `r + 1` the
binomial vanishes, above `n + 1` the bracket does.  (The general
`sum_range_choose_mul_of_eventually_zero`, against
`cBracket_eq_zero_of_ge`.) -/
theorem sum_choose_cBracket_range_eq (n r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (r.choose k : ℚ) * cBracket n k =
      ∑ k ∈ Finset.range (n + 2), (r.choose k : ℚ) * cBracket n k :=
  sum_range_choose_mul_of_eventually_zero
    (fun _k hk => cBracket_eq_zero_of_ge hk) r

/-- **Deliverable (a), the expansion** (`eq:delta0-expansion`): with all
gaps zero, the chained count over `r + 1` components (`r` gaps, the
manuscript's rank `r + 1`) is `∑_{k=0}^{n+1} C(r,k) cₖ` — over ℚ, cast
once.  Unconditional in `d`: any gap vector with all gaps zero. -/
theorem cast_card_chainedTuples_of_gaps_eq_zero (n r : ℕ)
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => (0 : ℤ)) :
    (#(chainedTuples n (r + 1) d) : ℚ) =
      ∑ k ∈ Finset.range (n + 2), (r.choose k : ℚ) * cBracket n k := by
  rw [card_chainedTuples, hd, Tprod_zero_gaps, cast_vecMul_pow_dot,
    map_Tmat_zero_eq, add_comm (Nmat n) (1 : Matrix _ _ ℚ),
    vecMul_one_add_pow_dotProduct]
  exact sum_choose_cBracket_range_eq n r

/-! ## The polynomial — deliverable (b)

`delta0Poly n` is built explicitly in the binomial basis: the `k`-th
summand is `(cₖ/k!) · (descPochhammer ℚ k).comp (X − 1)`, whose value at
`X = rank` is `C(rank − 1, k) · cₖ` and whose degree is `k` (with leading
coefficient `cₖ/k!`).  The degrees are pairwise distinct, so the top
non-vanishing bracket `c_{n+1}` fixes degree and leading coefficient. -/

open Polynomial in
/-- The counting polynomial of `thm-delta0-degrees` (improper half),
explicitly in the binomial basis. -/
noncomputable def delta0Poly (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n + 2),
    Polynomial.C (cBracket n k / k.factorial) *
      (descPochhammer ℚ k).comp (Polynomial.X - Polynomial.C 1)

open Polynomial in
/-- The evaluation of `delta0Poly` at the rank `r + 1`: the binomial-basis
values `C(r, k)` appear, matching the expansion. -/
theorem delta0Poly_eval_natCast (n r : ℕ) :
    (delta0Poly n).eval ((r + 1 : ℕ) : ℚ) =
      ∑ k ∈ Finset.range (n + 2), (r.choose k : ℚ) * cBracket n k := by
  rw [delta0Poly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have harg : ((r + 1 : ℕ) : ℚ) - 1 = (r : ℚ) := by push_cast; ring
  rw [harg]
  have hk : (k.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have heval : (descPochhammer ℚ k).eval (r : ℚ) =
      (r.choose k : ℚ) * k.factorial := by
    rw [Nat.cast_choose_eq_descPochhammer_div ℚ r k]
    field_simp
  rw [heval]
  field_simp

open Polynomial in
/-- Each binomial-basis summand has degree at most `k`. -/
theorem delta0Poly_summand_natDegree_le (n k : ℕ) :
    (Polynomial.C (cBracket n k / k.factorial) *
        (descPochhammer ℚ k).comp (Polynomial.X - Polynomial.C 1)).natDegree
      ≤ k := by
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
    Polynomial.natDegree_X_sub_C, mul_one]

open Polynomial in
/-- The top summand has degree exactly `n + 1` and leading coefficient
`c_{n+1}/(n+1)!`. -/
theorem delta0Poly_top_summand (n : ℕ) :
    (Polynomial.C (cBracket n (n + 1) / (n + 1).factorial) *
        (descPochhammer ℚ (n + 1)).comp
          (Polynomial.X - Polynomial.C 1)).natDegree = n + 1 ∧
      (Polynomial.C (cBracket n (n + 1) / (n + 1).factorial) *
        (descPochhammer ℚ (n + 1)).comp
          (Polynomial.X - Polynomial.C 1)).leadingCoeff =
        cBracket n (n + 1) / (n + 1).factorial := by
  have hc : cBracket n (n + 1) / ((n + 1).factorial : ℚ) ≠ 0 := by
    have h1 := cBracket_top_pos n
    have h2 : (0 : ℚ) < (n + 1).factorial := by
      exact_mod_cast (n + 1).factorial_pos
    positivity
  have hmon : ((descPochhammer ℚ (n + 1)).comp
      (Polynomial.X - Polynomial.C 1)).Monic :=
    (monic_descPochhammer ℚ (n + 1)).comp (monic_X_sub_C 1)
      (by rw [Polynomial.natDegree_X_sub_C]; omega)
  constructor
  · rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_comp,
      descPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one]
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hmon.leadingCoeff, mul_one]

open Polynomial in
/-- `thm-delta0-degrees`, improper half, degree clause: the degree is
**exactly** `n + 1` — for every `n : ℕ`, the printed `n ≥ 1` being
unnecessary. -/
theorem delta0Poly_natDegree (n : ℕ) : (delta0Poly n).natDegree = n + 1 := by
  have hsum : (∑ k ∈ Finset.range (n + 1),
      Polynomial.C (cBracket n k / k.factorial) *
        (descPochhammer ℚ k).comp
          (Polynomial.X - Polynomial.C 1)).natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
      le_trans (delta0Poly_summand_natDegree_le n k)
        (by rw [Finset.mem_range] at hk; omega)
  rw [delta0Poly, Finset.sum_range_succ,
    Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (lt_of_le_of_lt hsum (by rw [(delta0Poly_top_summand n).1]; omega))]
  exact (delta0Poly_top_summand n).1

open Polynomial in
/-- `thm-delta0-degrees`, improper half, leading-coefficient clause
(`eq:delta0-leading`, first formula): `(∏_{j=0}^{n} C(n,j)) / (n+1)!`. -/
theorem delta0Poly_leadingCoeff (n : ℕ) :
    (delta0Poly n).leadingCoeff =
      (∏ j ∈ Finset.range (n + 1), (n.choose j : ℚ)) /
        ((n + 1).factorial : ℚ) := by
  have hsum : (∑ k ∈ Finset.range (n + 1),
      Polynomial.C (cBracket n k / k.factorial) *
        (descPochhammer ℚ k).comp
          (Polynomial.X - Polynomial.C 1)).natDegree ≤ n :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
      le_trans (delta0Poly_summand_natDegree_le n k)
        (by rw [Finset.mem_range] at hk; omega)
  rw [delta0Poly, Finset.sum_range_succ,
    Polynomial.leadingCoeff_add_of_degree_lt
      (Polynomial.degree_lt_degree
        (lt_of_le_of_lt hsum
          (by rw [(delta0Poly_top_summand n).1]; omega)))]
  rw [(delta0Poly_top_summand n).2, cBracket_top]

/-! ## The headline statements -/

/-- **`thm-delta0-degrees`, improper half** (chained-count form,
unconditional): with all gaps zero, the count of chained tuples of rank
`r + 1` agrees with the explicit polynomial `delta0Poly n` evaluated at
the rank, and that polynomial has degree exactly `n + 1` with leading
coefficient `(∏_{j=0}^{n} C(n,j))/(n+1)!`.  Stated for every `n : ℕ` (the
printed `n ≥ 1` is unnecessary) and every rank `≥ 1`. -/
theorem thm_delta0_degrees_improper (n : ℕ) :
    ∃ p : Polynomial ℚ,
      (∀ (r : ℕ) (d : Fin (r + 1) → ℕ), (∀ i, d i = 0) →
        (#(chainedTuples n (r + 1) d) : ℚ) = p.eval ((r + 1 : ℕ) : ℚ)) ∧
      p.natDegree = n + 1 ∧
      p.leadingCoeff =
        (∏ j ∈ Finset.range (n + 1), (n.choose j : ℚ)) /
          ((n + 1).factorial : ℚ) := by
  refine ⟨delta0Poly n, fun r d hd => ?_, delta0Poly_natDegree n,
    delta0Poly_leadingCoeff n⟩
  rw [cast_card_chainedTuples_of_gaps_eq_zero n r
      (by funext i; simp [gaps, hd]),
    delta0Poly_eval_natCast]

/-- `thm-delta0-degrees`, improper half, in the printed `|FF(n;0,…,0)|`
form — modulo the same explicit surjectivity hypothesis as C2b
(`thm-chaining`'s open half), as it must be. -/
theorem cast_ncard_ffSetN_zero_eval (n r : ℕ)
    (hsurj : Set.SurjOn (Phi (fun _ : Fin (r + 1) => 0))
      {s : Fin (r + 1) → Fin (n + 1) → ℕ |
        (∀ i, s i ∈ Fn n) ∧ Chained (fun _ => 0) s}
      (ffSetN n (fun _ : Fin (r + 1) => 0))) :
    ((ffSetN n (fun _ : Fin (r + 1) => 0)).ncard : ℚ) =
      (delta0Poly n).eval ((r + 1 : ℕ) : ℚ) := by
  rw [card_ffSetN n r _ hsurj, ← card_chainedTuples,
    cast_card_chainedTuples_of_gaps_eq_zero n r
      (by funext i; simp [gaps]),
    delta0Poly_eval_natCast]

end ExteriorConvex
