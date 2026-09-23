# Rung D3c Lean numerical anchors — 2026-09-18 (jts-pc)

Sanity anchors for `LEAN/ExteriorConvex/Counting/ProperThreshold.lean`
(rung D3c: `prop-proper-threshold` and the proper half of
`prop-perron-threshold` as the eigenvalue restatement), run during
development via a scratch file (`LEAN/D3cCheck.lean`, deleted after the
run, per the rung convention that `#eval`s stay out of the formal
development; reproduce by recreating the file below and running
`cd LEAN && lake env lean D3cCheck.lean`).

**Entrywise, not totals**, per the standing verification standard.  The
one check that distinguishes a correct threshold from an off-by-one is
the **saturation boundary**: at `n = 3` the threshold is `δ ≥ n − 1 = 2`,
so `T′(2)` must equal `1⃗u⃗′` entrywise *and `T′(1)` must not* — the
proper analogue of D1's `T(4) = 1⃗u⃗ ≠ T(3)` check.  Both matrices were
read out in full (5×5, entrywise), and every count was computed **two
independent ways**: `Finset` enumeration of `properChainedTuples` and
the matrix product `u⃗′ T′(δ)⋯ 1⃗`.

## Expected vs. observed — all match

| quantity | expected (source) | observed |
|---|---|---|
| `upVec 3` entrywise | `[0,0,1,3,1]` (`u⃗′`, working note / D3a anchors) | `[0, 0, 1, 3, 1]` |
| `#(SnF 3)`, members | `5`; `(1,3,m,0)` for `m=0..3` and `(1,3,3,1)` | `5`; exactly those |
| `Tpmat 3 2` entrywise | every row `= u⃗′ = [0,0,1,3,1]` (saturation **on** at `δ = 2 = n−1`) | all five rows `[0,0,1,3,1]` |
| `Tpmat 3 1` entrywise | rows `τ = −1..2` saturated, row `τ = 3` **not**: `[0,0,0,1,1]` (bar `ρ > 2` kills `A′[1][2]`, `A′[2][2]`; saturation **off** at `δ = 1 = n−2`) | rows 0–3 `[0,0,1,3,1]`, row 4 `[0,0,0,1,1]` — differs at exactly the formal witness entry `(τ,τ') = (3,1)`: `0` vs `u′[1] = 1` |
| proper pairs, `n = 3`: `u⃗′T′(δ)1⃗` (matrix) | `25 = 5²` at `δ = 2, 3`; `22` at `δ = 1` (`eq:auto-18`) | `25`, `22` |
| proper pairs, `n = 3` (`Finset`, `d = (0,δ)`) | same | `25` (δ=2), `22` (δ=1), `25` (δ=3) |
| proper triples, `n = 3` | `125 = 5³` at `δ = (2,2)`; `< 125` at `δ = (1,1)`, both routes agreeing | `125`; `95` (Finset) `= 95` (matrix) |
| violating set at `n = 3`, `δ = n−2 = 1` | `{fullVec} ×ˢ {indeg = 2}` `= {(1,3,3,1)} × {(1,3,0,0),(1,3,1,0),(1,3,2,0)}` — 3 pairs, and `25 − 3 = 22` ✓ consistent | exactly those 3 pairs |
| proper pairs, `n = 2` (threshold `δ ≥ 1`) | `4 = 2²` at `δ = 1, 2` (`eq:auto-18` first entry); `3` at `δ = 0` (`eq:auto-17` first entry) | `4`, `3`, `4` |
| `\|FF_pr(2; 0^r)\|` (Finset, `r = 2,3,4` components) | `r + 1`: `3, 4, 5` | `3, 4, 5` |
| `n = 1` boundary (threshold reads `δ ≥ 0`) | `\|S_1\| = 1`, member `(1,1) = fullVec 1`; pairs at `δ = 0`: `1 = \|S_1\|²`; at gap `−1` (unsorted `d = (1,0)`): `0` — the ℤ-threshold is sharp even below ℕ | `1`; `{[1,1]}`; `1`; `0` |
| violating set at `n = 1`, `δ = n−2 = −1` | the product degenerates to the singleton `{(fullVec 1, fullVec 1)}` (the `indeg = 2` class of `S_1` is `{fullVec 1}`) | exactly `{([1,1],[1,1])}` |

Consistency notes: the `95` at `δ = (1,1)` was **not** an anchor
carried in from anywhere — the plan's anchors only demanded "strictly
less than 125" — and the file header initially guessed `110`; the two
independent computations agreed on `95` and the header was corrected.
The `n = 2` values `4`/`3` are the first entries of the manuscript's
`eq:auto-18`/`eq:auto-17` sequences, an independent cross-check against
`rem-proper-sequences`.

## The scratch file

```lean
-- Scratch anchor checks for rung D3c (deleted after the run).
-- Run: cd LEAN && lake env lean D3cCheck.lean
import ExteriorConvex.Counting.ProperThreshold

open Finset Matrix ExteriorConvex

#eval List.ofFn (upVec 3)
#eval #(SnF 3)
#eval (SnF 3).image (fun s => List.ofFn s)
#eval List.ofFn (fun k => List.ofFn (fun k' => Tpmat 3 2 k k'))
#eval List.ofFn (fun k => List.ofFn (fun k' => Tpmat 3 1 k k'))
#eval (upVec 3 ᵥ* Tpmat 3 2) ⬝ᵥ onesCol 3
#eval (upVec 3 ᵥ* Tpmat 3 1) ⬝ᵥ onesCol 3
#eval #(properChainedTuples 3 2 ![0, 2])
#eval #(properChainedTuples 3 2 ![0, 1])
#eval #(properChainedTuples 3 2 ![0, 3])
#eval #(properChainedTuples 3 3 ![0, 2, 4])
#eval #(properChainedTuples 3 3 ![0, 1, 2])
#eval ((upVec 3 ᵥ* Tpmat 3 1) ᵥ* Tpmat 3 1) ⬝ᵥ onesCol 3
#eval (((SnF 3) ×ˢ (SnF 3)).filter fun p =>
    ¬ top p.1 < (indeg p.2 : ℤ) + ((3 : ℤ) - 2)).image
  (fun p => (List.ofFn p.1, List.ofFn p.2))
#eval #(properChainedTuples 2 2 ![0, 1])
#eval #(properChainedTuples 2 2 ![0, 0])
#eval #(properChainedTuples 2 2 ![0, 2])
#eval #(properChainedTuples 2 3 ![0, 0, 0])
#eval #(properChainedTuples 2 4 ![0, 0, 0, 0])
#eval #(SnF 1)
#eval (SnF 1).image (fun s => List.ofFn s)
#eval #(properChainedTuples 1 2 ![0, 0])
#eval #(properChainedTuples 1 2 ![1, 0])
#eval (((SnF 1) ×ˢ (SnF 1)).filter fun p =>
    ¬ top p.1 < (indeg p.2 : ℤ) + ((1 : ℤ) - 2)).image
  (fun p => (List.ofFn p.1, List.ofFn p.2))
```

(One performance note for reproduction: `Finset.toList` is
noncomputable — use `.image` for readouts.  Stay at `n ≤ 3` and one
matrix per `#eval`, per the standing `Amat`-recomputation trap.)

## Axioms

`#print axioms` on all 14 public declarations of the file
(via a scratch `D3cAxioms.lean`, likewise deleted): every one exactly
`[propext, Classical.choice, Quot.sound]`.
