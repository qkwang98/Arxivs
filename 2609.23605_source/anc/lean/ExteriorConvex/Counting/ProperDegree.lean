/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D3d of the article-2 formalisation: the exact degree at `δ = 0`, proper half

Formalisation of the **proper half** of `thm-delta0-degrees` from
`article/exterior-convex_article2_draft_3.org` — the second half of
`eq:delta0-leading` — following the proof written in
`working-notes/delta0-exact-degrees-proof.org` (§"Proof of Theorem 2"),
per `working-notes/PLAN-formalise-D3-remaining.org` (part D3d, done
first of the three remaining parts, deliberately: this is the half
whose naive reduction *fails* and needed the invariant-block repair).

Rung D3b (`Counting/ProperBlock.lean`) staged everything structural:
the block `B = Bmat n` of `T′(0)` on `τ ∈ {1, …, n}`, its unit diagonal
and superdiagonal `C(n, i+2)`, the nilpotent part `N′ = NBmat n` with
`N′^n = 0`, and the entry point
`card_properChainedTuples_of_gaps_eq_zero`
(`count of rank r+1 = ũ⃗ B^r 1⃗`).  The Reduction and the Corner
evaluation are consumed **from the generic forms** of
`Counting/NilpotentReduction.lean` (`vecMul_one_add_pow_dotProduct`,
`sum_range_choose_mul_of_eventually_zero`,
`pow_apply_eq_zero_of_strictUpper`,
`pow_apply_staircase_of_strictUpper`) — the second consumer of the
refactor, as intended; nothing of D2's concrete `Nmat` layer is copied.

Contents, mirroring `Counting/Delta0.lean` in shape:

* **The one input D3b left missing, and it is load-bearing:
  `u′[1] = 1`** (`uTilde_zero`).  Per the working note:
  `u′[1] = ∑_{ρ≥2} A′[1][ρ] = A[1][2] = 1`, by `lem-A-structure`(1)
  (D1's `Amat_superdiag`) together with the support bound
  `ρ ≤ τ + 1 = 2` (`Apmat_eq_zero_of_add_one_lt`) — the unique proper
  vector with `tp = 1` being `(1, n, 0, …, 0)`.  In block terms:
  `ũ⃗[0] = 1`.  This is what makes the leading coefficient non-zero; it
  is used exactly once, in the corner evaluation `cpBracket_top` —
  nowhere else (the improper half's `uVec_zero` plays the same role in
  `cBracket_top`).
* *(a) the certified core*, the block brackets
  `cpBracket n k = ũ⃗ N′^k 1⃗`: `cpBracket_eq_zero_of_ge` (`= 0` for
  `k ≥ n`), `cpBracket_top`
  (`c′_{n−1} = ∏_{j=2}^{n} C(n,j)`, by the corner evaluation — only
  the full staircase `1 < 2 < ⋯ < n` survives) with
  `cpBracket_top_pos`, and the binomial expansion
  `cast_card_properChainedTuples_of_gaps_eq_zero`
  (`count = ∑_{k<n} C(r,k)·c′ₖ` for `r` gaps, all zero — the proper
  instance of `eq:delta0-expansion`, the manuscript's rank being the
  gap count plus one).
* *(b) the polynomial*, `delta0PolyPr n : Polynomial ℚ`, built in the
  same binomial basis as `delta0Poly`
  (`∑_{k<n} C(c′ₖ/k!)·(descPochhammer ℚ k).comp (X − 1)`):
  `delta0PolyPr_eval_natCast`, `delta0PolyPr_natDegree` (degree
  **exactly** `n − 1`), `delta0PolyPr_leadingCoeff`
  (`(∏_{j=2}^{n} C(n,j))/(n−1)!`, the second formula of
  `eq:delta0-leading`), and the bundled headline
  `thm_delta0_degrees_proper`, with the `|FF_pr|` form
  `cast_ncard_ffSetPrN_zero_eval` carrying D3a's explicit
  surjectivity/`lem-lexproper` hypothesis, as it must.

**Findings of the formalisation:**

* **`n ≥ 1` is genuinely needed, and this file shows exactly where** —
  the contrast with the improper half (where D2 found the printed
  `n ≥ 1` slack) is real.  At `n = 0` the block is empty, so every
  bracket is `0` while the empty product `∏_{j=2}^{0} C(0,j) = 1`:
  `cpBracket_top`, `cpBracket_top_pos` and the leading-coefficient
  clause are all *false* at `n = 0`, and each carries `1 ≤ n`.  One
  boundary subtlety worth recording: the bare degree clause
  `natDegree = n − 1` would be *degenerately true* at `n = 0` (the zero
  polynomial has `natDegree 0`, and ℕ-subtraction reads `n − 1 = 0`) —
  a truth by artifact, not by mathematics; the leading coefficient is
  the clause that honestly forces the boundary, and the bundled
  headline therefore requires `n ≥ 1` as the manuscript states.
* At `n = 1` everything degenerates as the working note's parenthetical
  says: the block is `1 × 1`, `N′ = 0`, the only bracket is
  `c′₀ = ũ⃗[0] = u′[1] = 1`, and the theorem reads degree `0`, leading
  coefficient `1/0! = 1` — the count is the constant `1 = |S_1|`.
* The generic reduction lemmas of `NilpotentReduction.lean` fit this
  consumer with no adaptation: the only new inputs were the staircase
  function `g a = C(n, a+2)` (from `NBmat_superdiag`) and `ũ⃗[0] = 1`.

**Out of scope, deliberately** (per the plan): D3c
(`prop-proper-threshold`, `λ_pr`), D3e (`prop-recurrence`), rung C3,
`lem-lexproper`, and anything spectral.

**`native_decide` is banned in this development** (it would add the
axiom `Lean.ofReduceBool`); the sanity anchors — at `n = 2` the
brackets `(c′₀, c′₁) = (2, 1)` and the block `N′ = [[0,1],[0,0]]`; at
`n = 3` the brackets `(c′₀, c′₁, c′₂) = (5, 7, 3)` with
`c′₂ = C(3,2)·C(3,3) = 3` and the expansion sums `5, 12, 22, 35` at
ranks `1–4` (second difference `3 = 2!·(3/2)`, the claimed leading
coefficient); at `n = 1` the single bracket `c′₀ = 1` — were `#eval`s
during development (recorded in
`runs/properdegree-lean-anchors-20260918.md`) and stay out of the
formal statements, deliberately.
-/
import ExteriorConvex.Counting.Proper
import ExteriorConvex.Counting.ProperBlock
import ExteriorConvex.Counting.NilpotentReduction

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## `u′[1] = 1`: the missing load-bearing input

The unique proper vector with `tp = 1` is `(1, n, 0, …, 0)`:
`u′[1] = ∑_{ρ} A′[1][ρ]`, and only `ρ = 2` survives — `ρ < 2` is zeroed
in `A′`, `ρ > 2 = τ + 1` is outside `A`'s support — leaving
`A[1][2] = 1` by `lem-A-structure`(1). -/

/-- **`u′[1] = 1`** (the working note's one still-missing input): in
block coordinates, `ũ⃗[0] = 1`.  This is what makes the leading
coefficient non-zero. -/
theorem uTilde_zero (hn : 0 < n) : uTilde n ⟨0, hn⟩ = 1 := by
  show upVec n (blockEmb n ⟨0, hn⟩) = 1
  have hτ : tauOf (blockEmb n ⟨0, hn⟩) = (1 : ℤ) := by
    simp only [tauOf, blockEmb_val]
    norm_num
  simp only [upVec, hτ]
  rw [Finset.sum_eq_single_of_mem (2 : ℤ)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun ρ _ hne => by
        rcases lt_or_ge ρ 2 with h2 | h2
        · exact Apmat_eq_zero_of_lt h2
        · exact Apmat_eq_zero_of_add_one_lt (by omega))]
  rw [Apmat_eq_of_le (by omega)]
  have h := Amat_superdiag n (j := 1) hn
  norm_num at h
  exact h

/-! ## The staircase machinery on the block

The general lemmas of `NilpotentReduction.lean`, instantiated at
`N′ = NBmat n` — the second consumer of the refactor, after `Nmat`. -/

/-- `N′` is strictly upper triangular, in the unbundled `val`-form the
general lemmas consume. -/
theorem NBmat_strictUpper (n : ℕ) :
    ∀ i j : Fin n, j.val ≤ i.val → NBmat n i j = 0 :=
  fun _i _j h => NBmat_apply_eq_zero_of_le h

/-- Powers of `N′` climb: `N′^k` vanishes below the `k`-th
superdiagonal.  (The general `pow_apply_eq_zero_of_strictUpper`, at
`N = NBmat n`.) -/
theorem NBmat_pow_apply_eq_zero :
    ∀ (k : ℕ) {i j : Fin n}, j.val < i.val + k →
      (NBmat n ^ k) i j = 0 :=
  pow_apply_eq_zero_of_strictUpper (NBmat_strictUpper n)

/-- **The corner evaluation on the block**: on the exact `k`-th
superdiagonal, `N′^k[i][i+k]` is the staircase product of superdiagonal
entries `C(n, ·+2)`.  (The general `pow_apply_staircase_of_strictUpper`
at `N = NBmat n`, with staircase function `g a = C(n, a+2)` from
`NBmat_superdiag`.) -/
theorem NBmat_pow_staircase :
    ∀ (k : ℕ) {i j : Fin n}, j.val = i.val + k →
      (NBmat n ^ k) i j =
        ∏ a ∈ Finset.range k, (n.choose (i.val + a + 2) : ℚ) :=
  pow_apply_staircase_of_strictUpper (NBmat_strictUpper n)
    (g := fun a => (n.choose (a + 2) : ℚ))
    (fun _a _h1 h2 => NBmat_superdiag h2)

/-! ## The block brackets `c′ₖ = ũ⃗ N′^k 1⃗` — deliverable (a) -/

/-- The block initial vector over ℚ. -/
def uTildeQ (n : ℕ) : Fin n → ℚ := fun i => (uTilde n i : ℚ)

/-- The proper brackets of the `δ = 0` expansion: `c′ₖ = ũ⃗ N′^k 1⃗`,
over ℚ, on the `n × n` block. -/
def cpBracket (n k : ℕ) : ℚ :=
  uTildeQ n ᵥ* NBmat n ^ k ⬝ᵥ (fun _ => (1 : ℚ))

/-- Deliverable (a), vanishing: `c′ₖ = 0` for `k ≥ n` — the block is
`n × n`, one better than the ambient `n + 2` (this is what the
invariant-block repair bought: degree `n − 1`, not `n + 1`). -/
theorem cpBracket_eq_zero_of_ge {k : ℕ} (h : n ≤ k) : cpBracket n k = 0 := by
  rw [cpBracket, pow_eq_zero_of_le h (NBmat_pow_eq_zero n),
    Matrix.vecMul_zero, zero_dotProduct]

/-- Deliverable (a), the top bracket: `c′_{n−1} = ũ⃗ N′^{n−1} 1⃗ =
∏_{j=2}^{n} C(n,j)` — the corner evaluation on the block.  The only
surviving entry of `N′^{n−1}` is the corner `(1, n)` (block `(0, n−1)`),
its value is the staircase product, and `ũ⃗[0] = u′[1] = 1` (the
**only** use of `uTilde_zero` in this file).  **`n ≥ 1` is genuinely
needed**: at `n = 0` the left side is the empty sum `0`, the right the
empty product `1`. -/
theorem cpBracket_top (n : ℕ) (hn : 1 ≤ n) :
    cpBracket n (n - 1) = ∏ j ∈ Finset.Icc 2 n, (n.choose j : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsub : m + 1 - 1 = m := Nat.add_sub_cancel m 1
  rw [hsub]
  have hIcc : ∏ j ∈ Finset.Icc 2 (m + 1), ((m + 1).choose j : ℚ) =
      ∏ a ∈ Finset.range m, ((m + 1).choose (a + 2) : ℚ) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    have hm : Order.succ (m + 1) - 2 = m := by
      simp [Order.succ_eq_add_one]
    rw [hm]
    exact Finset.prod_congr rfl fun a _ => by rw [Nat.add_comm 2 a]
  rw [hIcc, cpBracket, dotProduct]
  have hlast : (Fin.last m).val = m := rfl
  rw [Finset.sum_eq_single_of_mem (Fin.last m) (Finset.mem_univ _)
      (fun j _ hne => by
        have hjv : j.val ≠ m := fun hc => hne (Fin.ext hc)
        have hj := j.isLt
        have hz : (uTildeQ (m + 1) ᵥ* NBmat (m + 1) ^ m) j = 0 := by
          simp only [Matrix.vecMul, dotProduct]
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [NBmat_pow_apply_eq_zero m (by omega), mul_zero]
        rw [hz, zero_mul])]
  simp only [Matrix.vecMul, dotProduct, mul_one]
  rw [Finset.sum_eq_single_of_mem (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))
      (Finset.mem_univ _)
      (fun i _ hne => by
        have hiv : i.val ≠ 0 := fun hc => hne (Fin.ext hc)
        rw [NBmat_pow_apply_eq_zero m (by show m < i.val + m; omega),
          mul_zero])]
  rw [NBmat_pow_staircase m (by show m = 0 + m; omega)]
  rw [show uTildeQ (m + 1) ⟨0, Nat.succ_pos m⟩ = 1 from by
    rw [uTildeQ, uTilde_zero (Nat.succ_pos m), Nat.cast_one], one_mul]
  exact Finset.prod_congr rfl fun a _ => by
    show ((m + 1).choose (0 + a + 2) : ℚ) = _
    rw [Nat.zero_add]

/-- The top bracket is positive — every factor is a positive binomial
coefficient.  This is what makes the degree *exactly* `n − 1`. -/
theorem cpBracket_top_pos (n : ℕ) (hn : 1 ≤ n) : 0 < cpBracket n (n - 1) := by
  rw [cpBracket_top n hn]
  refine Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  exact_mod_cast Nat.choose_pos hj.2

/-! ## The expansion `count = ∑ₖ C(r,k) c′ₖ` — deliverable (a), third part

D3b's `card_properChainedTuples_of_gaps_eq_zero` gives the block
sandwich `ũ⃗ B^r 1⃗`; casting once into ℚ and applying the generic
binomial reduction to `B = I + N′` gives the proper instance of
`eq:delta0-expansion`.  Here `r` is the **gap count** — the
manuscript's rank is `r + 1`. -/

/-- Casting the ℕ-valued block sandwich `ũ⃗ B^r 1⃗` into ℚ. -/
theorem cast_vecMul_pow_dot_block (n r : ℕ) :
    ((uTilde n ᵥ* Bmat n ^ r ⬝ᵥ (fun _ => (1 : ℕ)) : ℕ) : ℚ) =
      uTildeQ n ᵥ* ((Bmat n).map (Nat.cast : ℕ → ℚ)) ^ r ⬝ᵥ
        (fun _ => (1 : ℚ)) := by
  have hmp : ((Bmat n).map (Nat.cast : ℕ → ℚ)) ^ r =
      (Bmat n ^ r).map (Nat.cast : ℕ → ℚ) := by
    rw [show (Nat.cast : ℕ → ℚ) = ⇑(Nat.castRingHom ℚ) from rfl,
      Matrix.map_pow]
  rw [hmp]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, uTildeQ, mul_one]
  push_cast
  rfl

/-- Truncation/extension of the expansion range: below `r + 1` the
binomial vanishes, above `n − 1` the bracket does.  (The general
`sum_range_choose_mul_of_eventually_zero`, against
`cpBracket_eq_zero_of_ge`.) -/
theorem sum_choose_cpBracket_range_eq (n r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (r.choose k : ℚ) * cpBracket n k =
      ∑ k ∈ Finset.range n, (r.choose k : ℚ) * cpBracket n k :=
  sum_range_choose_mul_of_eventually_zero
    (fun _k hk => cpBracket_eq_zero_of_ge hk) r

/-- **Deliverable (a), the expansion** (the proper instance of
`eq:delta0-expansion`): with all gaps zero, the proper chained count
over `r + 1` components (`r` gaps, the manuscript's rank `r + 1`) is
`∑_{k=0}^{n−1} C(r,k) c′ₖ` — over ℚ, cast once.  Unconditional in `d`
and in `n` (at `n = 0` both sides are `0`). -/
theorem cast_card_properChainedTuples_of_gaps_eq_zero (n r : ℕ)
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => (0 : ℤ)) :
    (#(properChainedTuples n (r + 1) d) : ℚ) =
      ∑ k ∈ Finset.range n, (r.choose k : ℚ) * cpBracket n k := by
  rw [card_properChainedTuples_of_gaps_eq_zero n r hd,
    cast_vecMul_pow_dot_block, map_Bmat_eq,
    add_comm (NBmat n) (1 : Matrix (Fin n) (Fin n) ℚ),
    vecMul_one_add_pow_dotProduct]
  exact sum_choose_cpBracket_range_eq n r

/-! ## The polynomial — deliverable (b)

`delta0PolyPr n` is built explicitly in the same binomial basis as the
improper `delta0Poly`: the `k`-th summand is
`(c′ₖ/k!) · (descPochhammer ℚ k).comp (X − 1)`, whose value at
`X = rank` is `C(rank − 1, k) · c′ₖ` and whose degree is `k`.  The
degrees are pairwise distinct, so the top non-vanishing bracket
`c′_{n−1}` fixes degree and leading coefficient. -/

open Polynomial in
/-- The counting polynomial of `thm-delta0-degrees` (proper half),
explicitly in the binomial basis. -/
noncomputable def delta0PolyPr (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range n,
    Polynomial.C (cpBracket n k / k.factorial) *
      (descPochhammer ℚ k).comp (Polynomial.X - Polynomial.C 1)

open Polynomial in
/-- The evaluation of `delta0PolyPr` at the rank `r + 1`: the
binomial-basis values `C(r, k)` appear, matching the expansion. -/
theorem delta0PolyPr_eval_natCast (n r : ℕ) :
    (delta0PolyPr n).eval ((r + 1 : ℕ) : ℚ) =
      ∑ k ∈ Finset.range n, (r.choose k : ℚ) * cpBracket n k := by
  rw [delta0PolyPr, Polynomial.eval_finsetSum]
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
theorem delta0PolyPr_summand_natDegree_le (n k : ℕ) :
    (Polynomial.C (cpBracket n k / k.factorial) *
        (descPochhammer ℚ k).comp (Polynomial.X - Polynomial.C 1)).natDegree
      ≤ k := by
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
    Polynomial.natDegree_X_sub_C, mul_one]

open Polynomial in
/-- The top summand has degree exactly `n − 1` and leading coefficient
`c′_{n−1}/(n−1)!` — `n ≥ 1` needed, through `cpBracket_top_pos`. -/
theorem delta0PolyPr_top_summand (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.C (cpBracket n (n - 1) / (n - 1).factorial) *
        (descPochhammer ℚ (n - 1)).comp
          (Polynomial.X - Polynomial.C 1)).natDegree = n - 1 ∧
      (Polynomial.C (cpBracket n (n - 1) / (n - 1).factorial) *
        (descPochhammer ℚ (n - 1)).comp
          (Polynomial.X - Polynomial.C 1)).leadingCoeff =
        cpBracket n (n - 1) / (n - 1).factorial := by
  have hc : cpBracket n (n - 1) / ((n - 1).factorial : ℚ) ≠ 0 := by
    have h1 := cpBracket_top_pos n hn
    have h2 : (0 : ℚ) < (n - 1).factorial := by
      exact_mod_cast (n - 1).factorial_pos
    positivity
  have hmon : ((descPochhammer ℚ (n - 1)).comp
      (Polynomial.X - Polynomial.C 1)).Monic :=
    (monic_descPochhammer ℚ (n - 1)).comp (monic_X_sub_C 1)
      (by rw [Polynomial.natDegree_X_sub_C]; omega)
  constructor
  · rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_comp,
      descPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one]
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hmon.leadingCoeff, mul_one]

open Polynomial in
/-- `thm-delta0-degrees`, proper half, degree clause: the degree is
**exactly** `n − 1` for `n ≥ 1`.  (At `n = 0` the statement would be
degenerately true — the zero polynomial has `natDegree 0` and
ℕ-subtraction reads `0 − 1 = 0` — but only as an artifact; the
hypothesis is kept because the *theorem*, degree plus leading
coefficient, genuinely fails at `n = 0`.) -/
theorem delta0PolyPr_natDegree (n : ℕ) (hn : 1 ≤ n) :
    (delta0PolyPr n).natDegree = n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have htop := delta0PolyPr_top_summand (m + 1) (by omega)
  simp only [Nat.add_sub_cancel] at htop ⊢
  rw [delta0PolyPr, Finset.sum_range_succ]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Finset.range_zero, Finset.sum_empty, zero_add]
    exact htop.1
  · have hsum : (∑ k ∈ Finset.range m,
        Polynomial.C (cpBracket (m + 1) k / k.factorial) *
          (descPochhammer ℚ k).comp
            (Polynomial.X - Polynomial.C 1)).natDegree ≤ m - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
        le_trans (delta0PolyPr_summand_natDegree_le (m + 1) k)
          (by rw [Finset.mem_range] at hk; omega)
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (lt_of_le_of_lt hsum (by rw [htop.1]; omega))]
    exact htop.1

open Polynomial in
/-- `thm-delta0-degrees`, proper half, leading-coefficient clause
(`eq:delta0-leading`, second formula): `(∏_{j=2}^{n} C(n,j)) / (n−1)!`.
This is the clause that genuinely needs `n ≥ 1`: at `n = 0` the zero
polynomial's leading coefficient is `0`, not the empty product `1`. -/
theorem delta0PolyPr_leadingCoeff (n : ℕ) (hn : 1 ≤ n) :
    (delta0PolyPr n).leadingCoeff =
      (∏ j ∈ Finset.Icc 2 n, (n.choose j : ℚ)) /
        ((n - 1).factorial : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have htop := delta0PolyPr_top_summand (m + 1) (by omega)
  have hbr := cpBracket_top (m + 1) (by omega)
  simp only [Nat.add_sub_cancel] at htop hbr ⊢
  rw [delta0PolyPr, Finset.sum_range_succ]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Finset.range_zero, Finset.sum_empty, zero_add, htop.2, hbr]
  · have hsum : (∑ k ∈ Finset.range m,
        Polynomial.C (cpBracket (m + 1) k / k.factorial) *
          (descPochhammer ℚ k).comp
            (Polynomial.X - Polynomial.C 1)).natDegree ≤ m - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
        le_trans (delta0PolyPr_summand_natDegree_le (m + 1) k)
          (by rw [Finset.mem_range] at hk; omega)
    rw [Polynomial.leadingCoeff_add_of_degree_lt
        (Polynomial.degree_lt_degree
          (lt_of_le_of_lt hsum (by rw [htop.1]; omega))),
      htop.2, hbr]

/-! ## The headline statements -/

/-- **`thm-delta0-degrees`, proper half** (chained-count form,
unconditional in `d`): for `n ≥ 1`, with all gaps zero, the count of
proper chained tuples of rank `r + 1` agrees with the explicit
polynomial `delta0PolyPr n` evaluated at the rank, and that polynomial
has degree exactly `n − 1` with leading coefficient
`(∏_{j=2}^{n} C(n,j))/(n−1)!` — the second half of `eq:delta0-leading`.
Unlike the improper half, `n ≥ 1` is genuinely needed (the leading
coefficient fails at `n = 0`), matching the printed hypothesis. -/
theorem thm_delta0_degrees_proper (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      (∀ (r : ℕ) (d : Fin (r + 1) → ℕ), (∀ i, d i = 0) →
        (#(properChainedTuples n (r + 1) d) : ℚ) =
          p.eval ((r + 1 : ℕ) : ℚ)) ∧
      p.natDegree = n - 1 ∧
      p.leadingCoeff =
        (∏ j ∈ Finset.Icc 2 n, (n.choose j : ℚ)) /
          ((n - 1).factorial : ℚ) := by
  refine ⟨delta0PolyPr n, fun r d hd => ?_, delta0PolyPr_natDegree n hn,
    delta0PolyPr_leadingCoeff n hn⟩
  rw [cast_card_properChainedTuples_of_gaps_eq_zero n r
      (by funext i; simp [gaps, hd]),
    delta0PolyPr_eval_natCast]

/-- `thm-delta0-degrees`, proper half, in the printed `|FF_pr(n;0,…,0)|`
form — modulo the same explicit surjectivity/`lem-lexproper` hypothesis
as D3a's `card_ffSetPrN`, as it must be. -/
theorem cast_ncard_ffSetPrN_zero_eval (n r : ℕ) (hn : 1 ≤ n)
    (hsurj : Set.SurjOn (Phi (fun _ : Fin (r + 1) => 0))
      {s : Fin (r + 1) → Fin (n + 1) → ℕ |
        (∀ i, s i ∈ SnF n) ∧ Chained (fun _ => 0) s}
      (ffSetPrN n (fun _ : Fin (r + 1) => 0))) :
    ((ffSetPrN n (fun _ : Fin (r + 1) => 0)).ncard : ℚ) =
      (delta0PolyPr n).eval ((r + 1 : ℕ) : ℚ) := by
  rw [card_ffSetPrN n r hn _ hsurj, ← card_properChainedTuples,
    cast_card_properChainedTuples_of_gaps_eq_zero n r
      (by funext i; simp [gaps]),
    delta0PolyPr_eval_natCast]

end ExteriorConvex
