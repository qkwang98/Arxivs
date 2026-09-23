/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D3e of the article-2 formalisation: `prop-recurrence`, the recurrence half

Formalisation of the **recurrence half** of `prop-recurrence` from
`article/exterior-convex_article2_draft_3.org`, per
`working-notes/PLAN-formalise-D3-remaining.org` (D3e) and
`working-notes/PLAN-formalise-article2.org` (§D3e): for a constant gap
`δ`, the sequence `a_r = u⃗ T(δ)^{r−1} 1⃗` satisfies the linear recurrence
whose characteristic polynomial is that of `T(δ)` — and the same for the
proper count with `T′(δ)`.  The proof is the manuscript's own:
Cayley–Hamilton (`Matrix.aeval_self_charpoly`) applied to `T(δ)`,
sandwiched between `u⃗` and `1⃗`.  No spectral theory anywhere.

**Index dictionary.** `aSeq n δ j = u⃗ T(δ)^j 1⃗` is the manuscript's
`a_r` at rank `r = j + 1` (so `aSeq 0 = a_1 = |𝓕_n|`); the count-level
statements are phrased at rank `m + 1` with `m` the gap count, as
everywhere in rungs C2–D3.

Contents, in four layers per side (improper `T`, proper `T′`):

* **The recurrence** (`aSeq_recurrence` / `apSeq_recurrence`): for every
  `k`, `∑_{i=0}^{deg} p.coeff i · a_{k+i} = 0` with `p` the
  characteristic polynomial — the generic Cayley–Hamilton sandwich
  `sandwich_charpoly_recurrence`, instantiated.
* **Degree and monicity** (`TQ_charpoly_natDegree`,
  `TQ_charpoly_coeff_top`, and the `Tp`-versions): `deg p = n + 2` and
  `p.coeff (n+2) = 1`, so the vanishing combination above really *is* a
  recurrence of order `n + 2` — monicity is what lets the top term be
  solved for (`aSeq_solved` / `apSeq_solved`), which is what "satisfies
  the linear recurrence" means operationally.
* **The bridge to the count** — without which this file would be a
  linear-algebra exercise, not `prop-recurrence`: at constant gap the
  transfer product collapses to a power (`Tprod_const_gaps` /
  `Tpprod_const_gaps`), so rung C2's unconditional counting identity
  reads `|chained tuples at rank m+1| = aSeq m`
  (`cast_card_chainedTuples_of_gaps_const`, proper
  `cast_card_properChainedTuples_of_gaps_const`), and the ℕ-valued counts
  themselves satisfy the recurrence
  (`card_chainedTuples_constGap_recurrence` + `…_solved`, proper
  analogues) — **unconditionally**, even in `n`.  The manuscript's
  literal `a_r = |FF(n; 0, δ, 2δ, …)|` form is certified modulo the same
  explicit surjectivity hypothesis as `thm-main`/`thm-proper` (rung C3 +
  `lem-lexproper`, non-targets): `ncard_ffSetN_constGap_recurrence`,
  `ncard_ffSetPrN_constGap_recurrence`.
* **The `δ = 0` cross-check against rungs D2/D3b** (`TQ_zero_charpoly`,
  `TpQ_zero_charpoly`, and the finite-difference forms): `T(0)` is
  unipotent (`prop-delta0`), so its characteristic polynomial is
  `(X − 1)^{n+2}` and the recurrence says the `(n+2)`-th finite
  difference of `aSeq n 0` vanishes — `prop-delta0`'s "polynomial of
  degree ≤ n+1", independently re-derived.  `T′(0)` is **not** unipotent
  (rung D3b: eigenvalues `0, 0, 1, …, 1`); its characteristic polynomial
  is `X² (X − 1)^n`, and the recurrence becomes "the `n`-th finite
  difference of the twice-shifted proper sequence vanishes" — consistent
  with D3d's exact degree `n − 1`.  Cayley–Hamilton is indifferent to
  the non-unipotence, so **the proper recurrence needs no hypothesis the
  manuscript omits** — not even `n ≥ 1`.

**Explicitly out of scope, deliberately** (the plan's split, and §10.1
already records it): the **growth half** of `prop-recurrence`, `a_r ∼
C λ^r` with `λ` the Perron root.  That needs the Perron root to be the
*dominant* eigenvalue — Perron–Frobenius, which Mathlib does not have —
and unlike rung D4 there is no rank-one degeneracy below the threshold to
exploit, so there is no honest cheap restatement either.  Nothing in this
file mentions eigenvalues at all.

Design decision (per the plan, same as rung D2): `Matrix.charpoly` needs
a `CommRing`, and ℕ is only a semiring, so the ℕ-valued `Tmat`/`Tpmat`
are cast into ℚ **once**, at `TQ`/`TpQ`.  Beyond the typeclass there are
the two standing reasons recorded in `Delta0.lean`: over ℕ truncated
subtraction would silently corrupt the alternating-sign charpoly
coefficients, and ℕ-division floors — both failures that typecheck.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool` and break the three-standard-axioms property that
article 1's §10 asserts in print).  The numerical anchors — the
manuscript's `mex-recurrences` sequences `5, 20, 76, 285, 1065` (n = 2,
δ = 1, recurrence `a_r = 5a_{r−1} − 5a_{r−2} + a_{r−3}`) and `10, 69,
426, 2532, 14847` (n = 3, δ = 1), the δ = 0 sequences `10, 43, …` with
vanishing fifth difference, and the proper `5, 12, 22, 35, 51` — were
checked entrywise during development against the extracted matrices and
stay out of the formal statements; see
`runs/recurrence-lean-anchors-20260918.md`.
-/
import ExteriorConvex.Counting.Delta0
import ExteriorConvex.Counting.ProperBlock

open Finset Matrix Polynomial

namespace ExteriorConvex

variable {n : ℕ}

/-! ## Cayley–Hamilton, sandwiched: the generic recurrence

For any square matrix `M` over a commutative ring and any vectors `v⃗`,
`w⃗`, the sandwich sequence `j ↦ v⃗ M^j w⃗` satisfies the linear recurrence
whose characteristic polynomial is `M.charpoly`.  Stated generically,
like `NilpotentReduction.lean`'s lemmas, because it is applied four times
below (two matrices × two conclusions). -/

section Generic

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sandwiching `M^k · p(M)` between two vectors expands into the linear
combination, with the coefficients of `p`, of the sandwich sequence
shifted by `k`.  (Linearity of `v⃗ (·) w⃗` over the `aeval` expansion of
`p`.) -/
theorem vecMul_pow_mul_aeval_dotProduct (M : Matrix ι ι R) (v w : ι → R)
    (p : Polynomial R) (k : ℕ) :
    v ᵥ* (M ^ k * Polynomial.aeval M p) ⬝ᵥ w =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * (v ᵥ* M ^ (k + i) ⬝ᵥ w) := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  simp_rw [mul_smul_comm, ← pow_add]
  rw [Matrix.vecMul_sum, sum_dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Matrix.vecMul_smul, smul_dotProduct, smul_eq_mul]

/-- **Cayley–Hamilton, sandwiched**: for every `k`,
`∑_{i=0}^{deg} charpoly.coeff i · (v⃗ M^{k+i} w⃗) = 0` — the sequence
`j ↦ v⃗ M^j w⃗` satisfies the linear recurrence whose characteristic
polynomial is that of `M`. -/
theorem sandwich_charpoly_recurrence (M : Matrix ι ι R) (v w : ι → R)
    (k : ℕ) :
    ∑ i ∈ Finset.range (M.charpoly.natDegree + 1),
      M.charpoly.coeff i * (v ᵥ* M ^ (k + i) ⬝ᵥ w) = 0 := by
  rw [← vecMul_pow_mul_aeval_dotProduct M v w M.charpoly k,
    Matrix.aeval_self_charpoly, mul_zero, Matrix.vecMul_zero,
    zero_dotProduct]

end Generic

/-! ## The ℚ-cast transfer matrices and the sandwich sequences -/

/-- The transfer matrix `T(δ)` over ℚ (cast once, as everywhere from rung
D2 on). -/
def TQ (n : ℕ) (δ : ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  (Tmat n δ).map (Nat.cast : ℕ → ℚ)

/-- The proper transfer matrix `T′(δ)` over ℚ. -/
def TpQ (n : ℕ) (δ : ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  (Tpmat n δ).map (Nat.cast : ℕ → ℚ)

/-- The proper initial vector `u⃗′` over ℚ, at full size `n + 2` (rung
D3b's `uTildeQ` is its restriction to the block; D2's `uQ` is the
improper one). -/
def upQ (n : ℕ) : Fin (n + 2) → ℚ := fun k => (upVec n k : ℚ)

/-- The improper sandwich sequence `aSeq n δ j = u⃗ T(δ)^j 1⃗` — the
manuscript's `a_{j+1}` (rank `j + 1`), over ℚ. -/
def aSeq (n : ℕ) (δ : ℤ) (j : ℕ) : ℚ :=
  uQ n ᵥ* TQ n δ ^ j ⬝ᵥ (fun _ => (1 : ℚ))

/-- The proper sandwich sequence `apSeq n δ j = u⃗′ T′(δ)^j 1⃗`. -/
def apSeq (n : ℕ) (δ : ℤ) (j : ℕ) : ℚ :=
  upQ n ᵥ* TpQ n δ ^ j ⬝ᵥ (fun _ => (1 : ℚ))

/-! ## Degree and monicity: the vanishing combination is a recurrence

The characteristic polynomial of an `(n+2) × (n+2)` matrix has degree
exactly `n + 2` and is monic, so the combination below has full order
`n + 2` and its top coefficient is the unit `1` — without which
`aSeq_recurrence` would assert a vanishing linear combination, not a
recurrence that *determines* the next term. -/

theorem TQ_charpoly_natDegree (n : ℕ) (δ : ℤ) :
    (TQ n δ).charpoly.natDegree = n + 2 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem TpQ_charpoly_natDegree (n : ℕ) (δ : ℤ) :
    (TpQ n δ).charpoly.natDegree = n + 2 := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem TQ_charpoly_monic (n : ℕ) (δ : ℤ) : (TQ n δ).charpoly.Monic :=
  Matrix.charpoly_monic _

theorem TpQ_charpoly_monic (n : ℕ) (δ : ℤ) : (TpQ n δ).charpoly.Monic :=
  Matrix.charpoly_monic _

/-- The leading coefficient, at its honest index: `p.coeff (n+2) = 1`. -/
theorem TQ_charpoly_coeff_top (n : ℕ) (δ : ℤ) :
    (TQ n δ).charpoly.coeff (n + 2) = 1 := by
  have h := (TQ_charpoly_monic n δ).coeff_natDegree
  rwa [TQ_charpoly_natDegree] at h

theorem TpQ_charpoly_coeff_top (n : ℕ) (δ : ℤ) :
    (TpQ n δ).charpoly.coeff (n + 2) = 1 := by
  have h := (TpQ_charpoly_monic n δ).coeff_natDegree
  rwa [TpQ_charpoly_natDegree] at h

/-! ## The recurrence, sequence level -/

/-- **`prop-recurrence`, recurrence half, improper, sequence level**: for
every `k`, `∑_{i=0}^{n+2} p.coeff i · a_{k+i} = 0` with `p` the
characteristic polynomial of `T(δ)`.  Unconditional — every `n : ℕ`,
every `δ : ℤ`. -/
theorem aSeq_recurrence (n : ℕ) (δ : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range ((TQ n δ).charpoly.natDegree + 1),
      (TQ n δ).charpoly.coeff i * aSeq n δ (k + i) = 0 :=
  sandwich_charpoly_recurrence (TQ n δ) (uQ n) (fun _ => (1 : ℚ)) k

/-- **`prop-recurrence`, recurrence half, proper, sequence level** — "The
same holds for the proper count with `T′(δ)`."  Also unconditional: the
non-unipotence of `T′(0)` (rung D3b) is no obstacle, Cayley–Hamilton
holding for every square matrix. -/
theorem apSeq_recurrence (n : ℕ) (δ : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range ((TpQ n δ).charpoly.natDegree + 1),
      (TpQ n δ).charpoly.coeff i * apSeq n δ (k + i) = 0 :=
  sandwich_charpoly_recurrence (TpQ n δ) (upQ n) (fun _ => (1 : ℚ)) k

/-- The improper recurrence in **solved form**: monicity expresses
`a_{k+n+2}` in the `n + 2` preceding terms — "satisfies the linear
recurrence" in the operational sense. -/
theorem aSeq_solved (n : ℕ) (δ : ℤ) (k : ℕ) :
    aSeq n δ (k + (n + 2)) =
      -∑ i ∈ Finset.range (n + 2),
        (TQ n δ).charpoly.coeff i * aSeq n δ (k + i) := by
  have h := aSeq_recurrence n δ k
  rw [TQ_charpoly_natDegree, Finset.sum_range_succ, TQ_charpoly_coeff_top,
    one_mul] at h
  linarith

/-- The proper recurrence in solved form. -/
theorem apSeq_solved (n : ℕ) (δ : ℤ) (k : ℕ) :
    apSeq n δ (k + (n + 2)) =
      -∑ i ∈ Finset.range (n + 2),
        (TpQ n δ).charpoly.coeff i * apSeq n δ (k + i) := by
  have h := apSeq_recurrence n δ k
  rw [TpQ_charpoly_natDegree, Finset.sum_range_succ,
    TpQ_charpoly_coeff_top, one_mul] at h
  linarith

/-! ## The bridge to the count

At constant gap the ordered transfer product collapses to a matrix power,
so rung C2's/D3a's unconditional counting identities identify `aSeq` and
`apSeq` with the ℕ-valued counts — this bridge is what makes the
recurrence a statement about `|FF(d⃗)|` rather than about matrix
powers. -/

/-- With every gap equal to `δ` the transfer product collapses to a
power (rung D2's `Tprod_zero_gaps`, at general `δ`). -/
theorem Tprod_const_gaps (n : ℕ) (δ : ℤ) :
    ∀ r : ℕ, Tprod n r (fun _ => δ) = Tmat n δ ^ r := by
  intro r
  induction r with
  | zero => rw [Tprod_zero, pow_zero]
  | succ r ih =>
    show Tprod n r (fun _ => δ) * Tmat n δ = Tmat n δ ^ (r + 1)
    rw [ih, pow_succ]

/-- The proper analogue (rung D3b's `Tpprod_zero_gaps`, at general
`δ`). -/
theorem Tpprod_const_gaps (n : ℕ) (δ : ℤ) :
    ∀ r : ℕ, Tpprod n r (fun _ => δ) = Tpmat n δ ^ r := by
  intro r
  induction r with
  | zero => rw [Tpprod_zero, pow_zero]
  | succ r ih =>
    show Tpprod n r (fun _ => δ) * Tpmat n δ = Tpmat n δ ^ (r + 1)
    rw [ih, pow_succ]

/-- Casting the ℕ-valued sandwich `u⃗ T(δ)^r 1⃗` into ℚ (rung D2's
`cast_vecMul_pow_dot`, at general `δ`). -/
theorem cast_vecMul_Tmat_pow_dot (n r : ℕ) (δ : ℤ) :
    ((uVec n ᵥ* (Tmat n δ ^ r) ⬝ᵥ onesCol n : ℕ) : ℚ) = aSeq n δ r := by
  have hmp : TQ n δ ^ r = (Tmat n δ ^ r).map (Nat.cast : ℕ → ℚ) := by
    rw [TQ, show (Nat.cast : ℕ → ℚ) = ⇑(Nat.castRingHom ℚ) from rfl,
      Matrix.map_pow]
  rw [aSeq, hmp]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, uQ, onesCol,
    mul_one]
  push_cast
  rfl

/-- The proper cast. -/
theorem cast_vecMul_Tpmat_pow_dot (n r : ℕ) (δ : ℤ) :
    ((upVec n ᵥ* (Tpmat n δ ^ r) ⬝ᵥ onesCol n : ℕ) : ℚ) = apSeq n δ r := by
  have hmp : TpQ n δ ^ r = (Tpmat n δ ^ r).map (Nat.cast : ℕ → ℚ) := by
    rw [TpQ, show (Nat.cast : ℕ → ℚ) = ⇑(Nat.castRingHom ℚ) from rfl,
      Matrix.map_pow]
  rw [apSeq, hmp]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, upQ, onesCol,
    mul_one]
  push_cast
  rfl

/-- **The bridge, improper** (unconditional, rung C2's identity at
constant gap): `|chained tuples at rank r+1| = aSeq r`, for *any* degree
vector whose gaps are constantly `δ`. -/
theorem cast_card_chainedTuples_of_gaps_const (n r : ℕ) {δ : ℤ}
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => δ) :
    (#(chainedTuples n (r + 1) d) : ℚ) = aSeq n δ r := by
  rw [card_chainedTuples, hd, Tprod_const_gaps, cast_vecMul_Tmat_pow_dot]

/-- **The bridge, proper** (unconditional, rung D3a's identity at
constant gap): `|proper chained tuples at rank r+1| = apSeq r`. -/
theorem cast_card_properChainedTuples_of_gaps_const (n r : ℕ) {δ : ℤ}
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => δ) :
    (#(properChainedTuples n (r + 1) d) : ℚ) = apSeq n δ r := by
  rw [card_properChainedTuples, hd, Tpprod_const_gaps,
    cast_vecMul_Tpmat_pow_dot]

/-- The canonical constant-gap degree vector of `prop-recurrence`:
`d⃗ = (0, δ, 2δ, …)`. -/
def constGapD (δ : ℕ) (r : ℕ) : Fin r → ℕ := fun i => δ * i.val

/-- The gaps of `constGapD` are constantly `δ`. -/
theorem gaps_constGapD (δ r : ℕ) :
    gaps (constGapD δ (r + 1)) = fun _ => (δ : ℤ) := by
  funext i
  simp only [gaps, constGapD, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

/-! ## The recurrence, count level -/

/-- **`prop-recurrence`, recurrence half, improper, count level**
(unconditional): the ℕ-valued chained-tuple counts at the degree vectors
`(0, δ, …, mδ)` — the certified side of the manuscript's `a_r` —
satisfy the linear recurrence whose characteristic polynomial is that of
`T(δ)`. -/
theorem card_chainedTuples_constGap_recurrence (n δ k : ℕ) :
    ∑ i ∈ Finset.range ((TQ n (δ : ℤ)).charpoly.natDegree + 1),
      (TQ n (δ : ℤ)).charpoly.coeff i *
        (#(chainedTuples n (k + i + 1) (constGapD δ (k + i + 1))) : ℚ) =
      0 := by
  have h := aSeq_recurrence n (δ : ℤ) k
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cast_card_chainedTuples_of_gaps_const n (k + i)
      (gaps_constGapD δ (k + i))]

/-- The count-level recurrence in solved form: the count at rank
`k + n + 3` is determined by the `n + 2` preceding ranks. -/
theorem card_chainedTuples_constGap_solved (n δ k : ℕ) :
    (#(chainedTuples n (k + n + 3) (constGapD δ (k + n + 3))) : ℚ) =
      -∑ i ∈ Finset.range (n + 2),
        (TQ n (δ : ℤ)).charpoly.coeff i *
          (#(chainedTuples n (k + i + 1) (constGapD δ (k + i + 1))) : ℚ) := by
  have hb : (#(chainedTuples n (k + n + 3) (constGapD δ (k + n + 3))) : ℚ) =
      aSeq n (δ : ℤ) (k + (n + 2)) :=
    cast_card_chainedTuples_of_gaps_const n (k + n + 2)
      (gaps_constGapD δ (k + n + 2))
  rw [hb, aSeq_solved]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
  rw [cast_card_chainedTuples_of_gaps_const n (k + i)
    (gaps_constGapD δ (k + i))]

/-- The proper count-level recurrence (unconditional — no `n ≥ 1`, in
contrast to every conditional `|FF_pr|` statement of rung D3). -/
theorem card_properChainedTuples_constGap_recurrence (n δ k : ℕ) :
    ∑ i ∈ Finset.range ((TpQ n (δ : ℤ)).charpoly.natDegree + 1),
      (TpQ n (δ : ℤ)).charpoly.coeff i *
        (#(properChainedTuples n (k + i + 1)
          (constGapD δ (k + i + 1))) : ℚ) = 0 := by
  have h := apSeq_recurrence n (δ : ℤ) k
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cast_card_properChainedTuples_of_gaps_const n (k + i)
      (gaps_constGapD δ (k + i))]

/-- The proper count-level recurrence in solved form. -/
theorem card_properChainedTuples_constGap_solved (n δ k : ℕ) :
    (#(properChainedTuples n (k + n + 3) (constGapD δ (k + n + 3))) : ℚ) =
      -∑ i ∈ Finset.range (n + 2),
        (TpQ n (δ : ℤ)).charpoly.coeff i *
          (#(properChainedTuples n (k + i + 1)
            (constGapD δ (k + i + 1))) : ℚ) := by
  have hb : (#(properChainedTuples n (k + n + 3)
      (constGapD δ (k + n + 3))) : ℚ) =
      apSeq n (δ : ℤ) (k + (n + 2)) :=
    cast_card_properChainedTuples_of_gaps_const n (k + n + 2)
      (gaps_constGapD δ (k + n + 2))
  rw [hb, apSeq_solved]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
  rw [cast_card_properChainedTuples_of_gaps_const n (k + i)
    (gaps_constGapD δ (k + i))]

/-! ## The `|FF(d⃗)|` forms, modulo the standing surjectivity hypothesis

The manuscript's `a_r` is literally `|FF(n; 0, δ, 2δ, …)|`; identifying
that with the chained-tuple count is `thm-main`/`thm-proper`, certified in
rungs C2/D3a **modulo** the surjectivity half of `thm-chaining` (rung C3,
a non-target — open combinatorially, algebraic proof through Amata–Crupi
lex theory) plus, on the proper side, `lem-lexproper`.  The forms below
carry exactly that hypothesis, at each rank in the recurrence window. -/

/-- The `|FF(d⃗)|` bridge at constant gap, modulo C3's surjectivity —
rung C2's `card_ffSetN`, cast. -/
theorem cast_ncard_ffSetN_of_gaps_const (n r : ℕ) {δ : ℤ}
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => δ)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ | (∀ i, s i ∈ Fn n) ∧ Chained d s}
      (ffSetN n d)) :
    ((ffSetN n d).ncard : ℚ) = aSeq n δ r := by
  rw [card_ffSetN n r d hsurj, hd, Tprod_const_gaps,
    cast_vecMul_Tmat_pow_dot]

/-- The proper `|FF_pr(d⃗)|` bridge at constant gap, modulo the combined
surjectivity/`lem-lexproper` hypothesis and `n ≥ 1` — rung D3a's
`card_ffSetPrN`, cast. -/
theorem cast_ncard_ffSetPrN_of_gaps_const (n r : ℕ) (hn : 1 ≤ n) {δ : ℤ}
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => δ)
    (hsurj : Set.SurjOn (Phi d)
      {s : Fin (r + 1) → Fin (n + 1) → ℕ |
        (∀ i, s i ∈ SnF n) ∧ Chained d s}
      (ffSetPrN n d)) :
    ((ffSetPrN n d).ncard : ℚ) = apSeq n δ r := by
  rw [card_ffSetPrN n r hn d hsurj, hd, Tpprod_const_gaps,
    cast_vecMul_Tpmat_pow_dot]

/-- **`prop-recurrence`, recurrence half, improper, as printed**: the
manuscript's `a_r = |FF(n; 0, δ, 2δ, …)|` satisfies the linear recurrence
of `charpoly (T(δ))`, modulo `thm-chaining`'s surjectivity at each rank
in the window (the same standing hypothesis as `thm-main`, quantified
over ranks because the recurrence relates `n + 3` consecutive ones). -/
theorem ncard_ffSetN_constGap_recurrence (n δ k : ℕ)
    (hsurj : ∀ m : ℕ, Set.SurjOn (Phi (constGapD δ (m + 1)))
      {s : Fin (m + 1) → Fin (n + 1) → ℕ |
        (∀ i, s i ∈ Fn n) ∧ Chained (constGapD δ (m + 1)) s}
      (ffSetN n (constGapD δ (m + 1)))) :
    ∑ i ∈ Finset.range ((TQ n (δ : ℤ)).charpoly.natDegree + 1),
      (TQ n (δ : ℤ)).charpoly.coeff i *
        ((ffSetN n (constGapD δ (k + i + 1))).ncard : ℚ) = 0 := by
  have h := aSeq_recurrence n (δ : ℤ) k
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cast_ncard_ffSetN_of_gaps_const n (k + i)
      (gaps_constGapD δ (k + i)) (hsurj (k + i))]

/-- **`prop-recurrence`, recurrence half, proper, as printed**: `a′_r =
|FF_pr(n; 0, δ, 2δ, …)|` satisfies the recurrence of `charpoly (T′(δ))`,
modulo the combined surjectivity/`lem-lexproper` hypothesis at each rank
and `n ≥ 1` (both inherited from `thm-proper`; the recurrence itself
needs neither — see `apSeq_recurrence`). -/
theorem ncard_ffSetPrN_constGap_recurrence (n δ k : ℕ) (hn : 1 ≤ n)
    (hsurj : ∀ m : ℕ, Set.SurjOn (Phi (constGapD δ (m + 1)))
      {s : Fin (m + 1) → Fin (n + 1) → ℕ |
        (∀ i, s i ∈ SnF n) ∧ Chained (constGapD δ (m + 1)) s}
      (ffSetPrN n (constGapD δ (m + 1)))) :
    ∑ i ∈ Finset.range ((TpQ n (δ : ℤ)).charpoly.natDegree + 1),
      (TpQ n (δ : ℤ)).charpoly.coeff i *
        ((ffSetPrN n (constGapD δ (k + i + 1))).ncard : ℚ) = 0 := by
  have h := apSeq_recurrence n (δ : ℤ) k
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [cast_ncard_ffSetPrN_of_gaps_const n (k + i) hn
      (gaps_constGapD δ (k + i)) (hsurj (k + i))]

/-! ## The `δ = 0` cross-check against rungs D2/D3b/D3d

At `δ = 0` the recurrence must reproduce `prop-delta0`: `T(0)` is
unipotent, so its characteristic polynomial is `(X − 1)^{n+2}` and the
recurrence says the `(n+2)`-th finite difference of the sequence
vanishes — which is exactly "polynomial in the rank of degree at most
`n + 1`", rung D2's certified statement.  On the proper side `T′(0)` is
**not** unipotent (rung D3b): its two vanishing columns contribute the
factor `X²`, the characteristic polynomial is `X² (X − 1)^n`, and the
finite-difference form acquires the shift by `2` — consistent with rung
D3d's exact degree `n − 1` in place of `n + 1`. -/

/-- `T(0)` is upper triangular over ℚ (rung D2's triangularity, cast). -/
theorem TQ_zero_isUpperTriangular (n : ℕ) :
    (TQ n 0).IsUpperTriangular := fun i j hji => by
  have h : j < i := hji
  rw [TQ, Matrix.map_apply, Tmat_zero_eq_zero_of_lt h, Nat.cast_zero]

/-- The diagonal of `T(0)` over ℚ is all ones. -/
theorem TQ_zero_diag (k : Fin (n + 2)) : TQ n 0 k k = 1 := by
  rw [TQ, Matrix.map_apply, Tmat_zero_diag, Nat.cast_one]

/-- **The cross-check with rung D2**: the characteristic polynomial of
`T(0)` is `(X − 1)^{n+2}` — the charpoly form of `prop-delta0`'s
unipotence. -/
theorem TQ_zero_charpoly (n : ℕ) :
    (TQ n 0).charpoly = (Polynomial.X - 1) ^ (n + 2) := by
  rw [Matrix.charpoly_of_isUpperTriangular _ (TQ_zero_isUpperTriangular n)]
  have h : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))),
      Polynomial.X - Polynomial.C (TQ n 0 i i) =
        Polynomial.X - 1 := fun i _ => by
    rw [TQ_zero_diag, Polynomial.C_1]
  rw [Finset.prod_congr rfl h, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- `T′(0)` is upper triangular over ℚ (rung D3b's triangularity,
cast). -/
theorem TpQ_zero_isUpperTriangular (n : ℕ) :
    (TpQ n 0).IsUpperTriangular := fun i j hji => by
  have h : j < i := hji
  rw [TpQ, Matrix.map_apply, Tpmat_zero_eq_zero_of_lt h, Nat.cast_zero]

/-- The diagonal of `T′(0)` at the two boundary indices is `0` — rung
D3b's vanishing columns `τ′ ∈ {−1, 0}`, on the diagonal. -/
theorem TpQ_zero_diag_boundary {k : Fin (n + 2)} (h : k.val ≤ 1) :
    TpQ n 0 k k = 0 := by
  rw [TpQ, Matrix.map_apply, Tpmat_apply_eq_zero_of_le_one 0 k h,
    Nat.cast_zero]

/-- The diagonal of `T′(0)` on the block `τ ∈ {1, …, n}` is `1` — rung
D3b's `Bmat_diag`, read back at full size. -/
theorem TpQ_zero_diag_block {k : Fin (n + 2)} (h : 2 ≤ k.val) :
    TpQ n 0 k k = 1 := by
  have hlt : k.val - 2 < n := by have := k.isLt; omega
  have hemb : blockEmb n ⟨k.val - 2, hlt⟩ = k := Fin.ext (by
    rw [blockEmb_val]
    show k.val - 2 + 2 = k.val
    omega)
  have hB : Tpmat n 0 k k = Bmat n ⟨k.val - 2, hlt⟩ ⟨k.val - 2, hlt⟩ := by
    rw [Bmat_apply, hemb]
  rw [TpQ, Matrix.map_apply, hB, Bmat_diag, Nat.cast_one]

/-- **The cross-check with rungs D3b/D3d**: the characteristic polynomial
of `T′(0)` is `X² (X − 1)^n` — `T′(0)` is *not* unipotent, its two zero
eigenvalues being rung D3b's vanishing columns `τ′ ∈ {−1, 0}`.
Cayley–Hamilton is indifferent, so the proper recurrence above holds
without any hypothesis the manuscript omits. -/
theorem TpQ_zero_charpoly (n : ℕ) :
    (TpQ n 0).charpoly =
      Polynomial.X ^ 2 * (Polynomial.X - 1) ^ n := by
  rw [Matrix.charpoly_of_isUpperTriangular _
    (TpQ_zero_isUpperTriangular n)]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h0 : TpQ n 0 (0 : Fin (n + 2)) 0 = 0 :=
    TpQ_zero_diag_boundary (by simp)
  have h1 : TpQ n 0 ((0 : Fin (n + 1)).succ) ((0 : Fin (n + 1)).succ) =
      0 :=
    TpQ_zero_diag_boundary (by simp)
  have hblock : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Polynomial.X - Polynomial.C (TpQ n 0 i.succ.succ i.succ.succ) =
        Polynomial.X - 1 := fun i _ => by
    rw [TpQ_zero_diag_block (show 2 ≤ i.val + 2 by omega),
      Polynomial.C_1]
  rw [h0, h1, Finset.prod_congr rfl hblock,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Polynomial.C_0, sub_zero]
  ring

/-- The `δ = 0` recurrence, written out: **the `(n+2)`-th finite
difference of the improper sandwich sequence vanishes** — exactly
`prop-delta0`'s "polynomial in the rank of degree at most `n + 1`",
re-derived through Cayley–Hamilton instead of rung D2's binomial
expansion.  At `n = 3`: the fifth finite difference of `10, 43, …`
vanishes. -/
theorem aSeq_zero_finite_difference (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 3),
      (-1 : ℚ) ^ (n + 2 - i) * ((n + 2).choose i : ℚ) *
        aSeq n 0 (k + i) = 0 := by
  have h := aSeq_recurrence n 0 k
  rw [TQ_charpoly_natDegree] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TQ_zero_charpoly, show (Polynomial.X - 1 : Polynomial ℚ) =
    Polynomial.X + Polynomial.C (-1) from by
      rw [Polynomial.C_neg, Polynomial.C_1]; ring,
    Polynomial.coeff_X_add_C_pow]

/-- The proper `δ = 0` recurrence, written out: **the `n`-th finite
difference of the twice-shifted proper sandwich sequence vanishes** — the
factor `X²` of `TpQ_zero_charpoly` becomes a shift by two ranks, and what
remains is `(X − 1)^n`, one degree of finite difference *less* than the
improper side, consistent with rung D3d's exact degree `n − 1` against
D2's `n + 1`. -/
theorem apSeq_zero_finite_difference (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - j) * (n.choose j : ℚ) *
        apSeq n 0 (k + 2 + j) = 0 := by
  have hXsub : (Polynomial.X - 1 : Polynomial ℚ) =
      Polynomial.X + Polynomial.C (-1) := by
    rw [Polynomial.C_neg, Polynomial.C_1]; ring
  have hdeg : ((Polynomial.X - 1 : Polynomial ℚ) ^ n).natDegree = n := by
    rw [hXsub, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C,
      mul_one]
  have hann : TpQ n 0 ^ (k + 2) *
      Polynomial.aeval (TpQ n 0)
        ((Polynomial.X - 1 : Polynomial ℚ) ^ n) = 0 := by
    have h := Matrix.aeval_self_charpoly (TpQ n 0)
    rw [TpQ_zero_charpoly, map_mul, map_pow, Polynomial.aeval_X] at h
    rw [pow_add, mul_assoc, h, mul_zero]
  have hexp := vecMul_pow_mul_aeval_dotProduct (TpQ n 0) (upQ n)
    (fun _ => (1 : ℚ)) ((Polynomial.X - 1 : Polynomial ℚ) ^ n) (k + 2)
  rw [hann, Matrix.vecMul_zero, zero_dotProduct, hdeg] at hexp
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hexp.symm
  rw [hXsub, Polynomial.coeff_X_add_C_pow]
  rfl

end ExteriorConvex
