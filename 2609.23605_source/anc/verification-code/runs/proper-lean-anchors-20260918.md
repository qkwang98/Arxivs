# Rung D3a/D3b Lean numerical anchors — 2026-09-18 (jts-pc)

Sanity anchors for `LEAN/ExteriorConvex/Counting/Proper.lean` (rung D3a:
the bridge, `A′`/`u⃗′`/`T′(δ)`, `thm-proper`'s counting identity) and
`LEAN/ExteriorConvex/Counting/ProperBlock.lean` (rung D3b: the
invariant-block repair), run during development via two scratch files
(`LEAN/D3Check.lean`, `LEAN/D3Check2.lean`, deleted after the run, per
the rung convention that `#eval`s stay out of the formal development;
reproduce by recreating the files below and running
`cd LEAN && lake env lean <file>`).

Two independent computations were compared, as in the D2 anchors
(`runs/delta0-lean-anchors-20260917.md`):

1. a **list-side re-implementation** of the matrix algebra over
   `List ℤ`, touching the formal development only through the raw
   entries `Tpmat n δ i j`, `Tmat n δ i j`, `upVec n k`, `uVec n k`,
   `Bmat n i j`, `uTilde n i` (each read exactly once — `Amat`
   recomputes `Fn n` per call, so matrix arithmetic must never be done
   on the formal `Matrix` values at `n = 3`);
2. the **formal `Finset` counts themselves**
   (`(properChainedTuples n r d).card`, `(chainedTuples n r d).card`,
   `(SnF n).card`), plus the formal block sandwich
   `uTilde 2 ᵥ* Bmat 2 ^ r ⬝ᵥ 1⃗` at `n = 2` where it is small enough
   to evaluate.

## Expected vs. observed — all match

| quantity | expected (source) | observed |
|---|---|---|
| `(SnF 3).card` | `5` (`\|S_3\| = 5`, manuscript) | `5` |
| `((Fn 3).filter (2 ≤ indeg ·)).card` | `5` (the bridge, `SnF_eq_filter_indeg`) | `5` |
| `(upL 3).sum` | `5` (`sum_upVec_eq_card_SnF`) | `5` |
| `u⃗′` at `n=3` | `(0, 0, 1, 3, 1)` — rows `τ = −1, 0` zeroed, `u′[1] = 1` (working note) | `[0, 0, 1, 3, 1]` |
| `ũ⃗` at `n=3` | `(1, 3, 1)` | `[1, 3, 1]` |
| `B` at `n=3` | unitriangular, superdiag `(C(3,2), C(3,3)) = (3, 1)` | `[[1,3,1],[0,1,1],[0,0,1]]` |
| `T′(0)` at `n=3` | columns `τ′ = −1, 0` identically zero; principal block = `B` | `[[0,0,1,3,1],[0,0,1,3,1],[0,0,1,3,1],[0,0,0,1,1],[0,0,0,0,1]]` |
| proper count, `n=3`, `r=2`, `δ=0` | `12` (`rem-proper-sequences`, `eq:auto-17`) | `12` |
| proper count, `n=3`, `r=2`, `δ=1` | `22` (`rem-proper-sequences`, `eq:auto-18`) | `22` |
| `(properChainedTuples 3 3 ![0,0,1]).card` | `45` (`eq:proper-not-reversible`) | `45` |
| `(properChainedTuples 3 3 ![0,1,1]).card` | `51` (`eq:proper-not-reversible`) | `51` |
| `(chainedTuples 3 3 ![0,0,1]).card` | `236` (improper, gap-reversal invariant) | `236` |
| `(chainedTuples 3 3 ![0,1,1]).card` | `236` | `236` |
| `u⃗′ T′(0) T′(1) 1⃗`, list side | `45` (`card_properChainedTuples` at `d=(0,0,1)`) | `45` |
| `u⃗′ T′(1) T′(0) 1⃗`, list side | `51` | `51` |
| `u⃗ T(0) T(1) 1⃗`, list side | `236` | `236` |
| `u⃗ T(1) T(0) 1⃗`, list side | `236` | `236` |
| `(properChainedTuples 2 rank 0).card`, ranks `1..4` | `[2, 3, 4, 5]` (`\|FF_pr(2;0^rank)\| = rank+1`) | `[2, 3, 4, 5]` |
| `uTilde 2 ᵥ* Bmat 2 ^ r ⬝ᵥ 1⃗`, `r = 0..3` (formal) | `[2, 3, 4, 5]` (D3b restriction at `n=2`) | `[2, 3, 4, 5]` |
| `ũ⃗ B^r 1⃗` at `n=3`, `r = 0..3`, list side | `[5, 12, 22, 35]` (proper poly `\tfrac32 r'^2+\tfrac52 r'+1` at rank `r' = r+1`… i.e. `5, 12, 22, 35`) | `[5, 12, 22, 35]` |
| `(properChainedTuples 3 3 ![0,0,0]).card` | `22` (matches block sandwich `r = 2`) | `22` |

Consistency notes: the proper counts `45 ≠ 51` against the equal
improper `236 = 236` reproduce exactly the gap-reversal asymmetry
`rem-proper-not-reversible` records — the formal `properChainedTuples`
sees the asymmetry, the formal `chainedTuples` does not.  The `n=3`
block sandwich `[5, 12, 22, 35]` agrees with the manuscript's proper
polynomial `\tfrac32 r^2 + \tfrac52 r + 1` at ranks `1, 2, 3, 4`, and
the Finset side agrees with the block side wherever both were computed
(`5, 12, 22` at `n=3`; all four ranks at `n=2`) — the two sides of
`card_properChainedTuples_of_gaps_eq_zero` observed equal, on top of
the theorem being proved.

## Scratch file 1 (list side + Finset side; the `#`-notation lines that
failed to parse in this file were rerun as file 2 with `.card` and
`open Finset Matrix`) — verbatim

```lean
import ExteriorConvex.Counting.ProperBlock

open ExteriorConvex

namespace D3Check

-- list-side extraction (touch each formal matrix entry once)
def TpL (n : ℕ) (δ : ℤ) : List (List ℤ) :=
  (List.finRange (n + 2)).map fun i =>
    (List.finRange (n + 2)).map fun j => ((Tpmat n δ i j : ℕ) : ℤ)

def TL (n : ℕ) (δ : ℤ) : List (List ℤ) :=
  (List.finRange (n + 2)).map fun i =>
    (List.finRange (n + 2)).map fun j => ((Tmat n δ i j : ℕ) : ℤ)

def upL (n : ℕ) : List ℤ :=
  (List.finRange (n + 2)).map fun k => ((upVec n k : ℕ) : ℤ)

def uL (n : ℕ) : List ℤ :=
  (List.finRange (n + 2)).map fun k => ((uVec n k : ℕ) : ℤ)

def BL (n : ℕ) : List (List ℤ) :=
  (List.finRange n).map fun i =>
    (List.finRange n).map fun j => ((Bmat n i j : ℕ) : ℤ)

def uTL (n : ℕ) : List ℤ :=
  (List.finRange n).map fun i => ((uTilde n i : ℕ) : ℤ)

def vecMulL (v : List ℤ) (M : List (List ℤ)) : List ℤ :=
  match M with
  | [] => []
  | r0 :: _ =>
    (List.range r0.length).map fun j =>
      ((v.zip M).map fun p => p.1 * (p.2.getD j 0)).sum

def iterVecMul (v : List ℤ) (M : List (List ℤ)) : ℕ → List ℤ
  | 0 => v
  | k + 1 => vecMulL (iterVecMul v M k) M

end D3Check

open D3Check

#eval (upL 3).sum                                     -- 5
#eval upL 3                                           -- [0, 0, 1, 3, 1]
#eval uTL 3                                           -- [1, 3, 1]
#eval BL 3                                            -- [[1,3,1],[0,1,1],[0,0,1]]
#eval TpL 3 0   -- columns 0 and 1 all-zero, block = BL 3
#eval (vecMulL (vecMulL (upL 3) (TpL 3 0)) (TpL 3 1)).sum   -- 45
#eval (vecMulL (vecMulL (upL 3) (TpL 3 1)) (TpL 3 0)).sum   -- 51
#eval (vecMulL (vecMulL (uL 3) (TL 3 0)) (TL 3 1)).sum      -- 236
#eval (vecMulL (vecMulL (uL 3) (TL 3 1)) (TL 3 0)).sum      -- 236
#eval (List.range 4).map fun r => (iterVecMul (uTL 3) (BL 3) r).sum
                                                      -- [5, 12, 22, 35]
```

## Scratch file 2 (Finset side) — verbatim

```lean
import ExteriorConvex.Counting.ProperBlock

open ExteriorConvex Finset Matrix

#eval (SnF 3).card                                    -- 5
#eval ((Fn 3).filter fun s => 2 ≤ indeg s).card       -- 5
#eval (properChainedTuples 3 2 ![0, 0]).card          -- 12
#eval (properChainedTuples 3 2 ![0, 1]).card          -- 22
#eval (properChainedTuples 3 3 ![0, 0, 1]).card       -- 45
#eval (properChainedTuples 3 3 ![0, 1, 1]).card       -- 51
#eval (chainedTuples 3 3 ![0, 0, 1]).card             -- 236
#eval (chainedTuples 3 3 ![0, 1, 1]).card             -- 236
#eval (List.range 4).map fun r =>
  (properChainedTuples 2 (r + 1) (fun _ => 0)).card   -- [2, 3, 4, 5]
#eval (List.range 4).map fun r =>
  uTilde 2 ᵥ* Bmat 2 ^ r ⬝ᵥ (fun _ => (1 : ℕ))        -- [2, 3, 4, 5]
#eval (properChainedTuples 3 3 ![0, 0, 0]).card       -- 22
```
