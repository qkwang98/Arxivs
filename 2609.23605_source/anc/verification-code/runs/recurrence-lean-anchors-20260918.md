# Rung D3e numerical anchors — `Counting/Recurrence.lean` (2026-09-18)

Entrywise checks run during the D3e formalisation (`prop-recurrence`, recurrence half).
Matrices and vectors were extracted **from the Lean definitions themselves** (`#eval` on
`Tmat`/`Tpmat`/`uVec`/`upVec`, one matrix per `#eval` per the standing performance budget);
the arithmetic on the extracted literals (sequence iteration, finite differences,
Faddeev–LeVerrier characteristic polynomials) was done in exact rational arithmetic in
Python. Per the standing convention these checks stay **out of the formal statements**
(`native_decide` is banned); the symbolic facts they cross-check (`TQ_zero_charpoly`,
`TpQ_zero_charpoly`, the recurrences) are proved for all `n` in the Lean file.

## Extracted matrices (ground truth from Lean)

Indexing `k = τ + 1`, i.e. rows/columns `τ ∈ {−1, 0, …, n}`.

```
uVec 2  = (1, 1, 2, 1)        |𝓕_2| = 5
uVec 3  = (1, 1, 3, 4, 1)     |𝓕_3| = 10     (the manuscript's u⃗)
upVec 3 = (0, 0, 1, 3, 1)     |S_3|  = 5     (the manuscript's u⃗′)

Tmat 2 1  = [[1,1,2,1],[1,1,2,1],[0,1,2,1],[0,0,1,1]]
Tmat 3 0  = [[1,1,3,4,1],[0,1,3,4,1],[0,0,1,3,1],[0,0,0,1,1],[0,0,0,0,1]]
Tmat 3 1  = [[1,1,3,4,1],[1,1,3,4,1],[0,1,3,4,1],[0,0,1,3,1],[0,0,0,1,1]]
Tpmat 3 0 = [[0,0,1,3,1],[0,0,1,3,1],[0,0,1,3,1],[0,0,0,1,1],[0,0,0,0,1]]
Tpmat 3 1 = [[0,0,1,3,1],[0,0,1,3,1],[0,0,1,3,1],[0,0,1,3,1],[0,0,0,1,1]]
```

`Tmat 3 0` is unipotent upper triangular with superdiagonal `(1,3,3,1)` (rung D2);
`Tpmat 3 0` has diagonal `(0,0,1,1,1)` — *not* unipotent, the two vanishing columns of
rung D3b.

## Sequences `a_r = u⃗ T(δ)^{r−1} 1⃗` (r = 1, 2, …)

```
n=2 δ=1 improper: 5, 20, 76, 285, 1065, 3976, 14840     (mex-recurrences: 5,20,76,285,1065 ✓)
n=3 δ=0 improper: 10, 43, 125, 290, 581, 1050, 1758, 2775
n=3 δ=1 improper: 10, 69, 426, 2532, 14847, 86634, ...  (mex-recurrences: 10,69,426,2532,14847 ✓)
n=3 δ=0 proper:   5, 12, 22, 35, 51, 70, 92, 117        (D3d's quadratic 5,12,22,35 ✓)
n=3 δ=1 proper:   5, 22, 95, 409, 1760, 7573, ...
```

**Finset cross-check (matrix-free, rank 2):** `#(chainedTuples 3 2 d)` = 43 at `d=(0,0)`,
69 at `d=(0,1)`; `#(properChainedTuples 3 2 d)` = 12 and 22 — all four matching the
matrix-side values above and the task anchors (`|FF(3;0,0)| = 43`, `|FF(3;0,1)| = 69`,
proper 12 and 22).

## Characteristic polynomials (Faddeev–LeVerrier on the extracted matrices)

```
T(1),  n=2: x⁴ − 5x³ + 5x² − x        = x(x−1)(x²−4x+1)   -- manuscript mex-recurrences, exact ✓
T(0),  n=3: x⁵ − 5x⁴ + 10x³ − 10x² + 5x − 1 = (x−1)⁵      -- TQ_zero_charpoly at n=3, coefficientwise ✓
T(1),  n=3: x⁵ − 9x⁴ + 21x³ − 15x² + 3x                   -- = x·(x⁴−9x³+21x²−15x+3), see note below
T′(0), n=3: x⁵ − 3x⁴ + 3x³ − x²       = x²(x−1)³          -- TpQ_zero_charpoly at n=3, coefficientwise ✓
T′(1), n=3: x⁵ − 5x⁴ + 3x³            = x³(x²−5x+3)
```

**Note on `mex-recurrences` at n = 3, δ = 1.** The manuscript says "the polynomial is
\(\lambda^4-9\lambda^3+21\lambda^2-15\lambda+3\)". The characteristic polynomial of the
5×5 matrix `T(1)` is that quartic **times λ** (constant term of the quartic is 3 ≠ 0, and
`T(1)` is singular). The printed order-4 recurrence `a_r = 9a_{r−1} − 21a_{r−2} +
15a_{r−3} − 3a_{r−4}` is exactly what Cayley–Hamilton on the quintic gives (the λ factor
is a rank shift, coefficient of `a_{r−5}` being 0), so the recurrence and the checked
values are correct as printed; only the noun "the polynomial", if read as "the
characteristic polynomial", is off by the factor λ. Reported, manuscript untouched.

## Recurrence checks (all exact, all zero)

- n=2 δ=1: printed recurrence `a_r = 5a_{r−1} − 5a_{r−2} + a_{r−3}` — residuals 0 for
  r = 4..7; full order-4 Cayley–Hamilton residuals 0.
- n=3 δ=1: printed order-4 recurrence — residuals 0 for r = 5..7; full order-5
  Cayley–Hamilton residual 0.
- n=3 δ=0 improper: **fifth finite difference of `10, 43, 125, 290, 581, 1050, 1758,
  2775` vanishes** (two windows checked) — the `aSeq_zero_finite_difference` cross-check
  against `prop-delta0`/rung D2, numerically.
- n=3 δ=0 proper: **third finite difference of the twice-shifted sequence vanishes**
  (`apSeq_zero_finite_difference` at n = 3: `(E−1)³E² a′ = 0` on `5, 12, 22, 35, 51,
  70, 92, 117`), and the full order-5 recurrence of `x²(x−1)³` has residual 0 —
  consistent with rung D3d's exact degree 2 = n − 1.
- n=3 δ=1 proper: full order-5 Cayley–Hamilton residual 0 on `5, 22, 95, 409, 1760,
  7573`.
