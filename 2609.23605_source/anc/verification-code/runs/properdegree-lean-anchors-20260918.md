# Rung D3d Lean numerical anchors — 2026-09-18 (jts-pc)

Sanity anchors for `LEAN/ExteriorConvex/Counting/ProperDegree.lean`
(rung D3d: the proper exact degree at `δ = 0`, the second half of
`eq:delta0-leading`), run during development via a scratch file
(`LEAN/D3dCheck.lean`, deleted after the run, per the rung convention
that `#eval`s stay out of the formal development; reproduce by
recreating the file below and running `cd LEAN && lake env lean
D3dCheck.lean`).

**Entrywise, not totals**, per the standing verification standard.  As
in the D3a/D3b anchors (`runs/proper-lean-anchors-20260918.md`): the
`n = 3` layer never does matrix arithmetic on the formal `Matrix`
values (`Amat` recomputes `Fn n` per call) — the formal entries of
`Bmat 3`/`uTilde 3` are each read exactly once and compared to the
expected literals, and the bracket/expansion arithmetic is an
independent re-implementation over `List Int` on those verified
literals.  The `n = 2` and `n = 1` layers are small enough to evaluate
the formal `cpBracket`/`NBmat`/`properChainedTuples` directly.

## Expected vs. observed — all match

| quantity | expected (source) | observed |
|---|---|---|
| `Bmat 3` entrywise | `[[1,3,1],[0,1,1],[0,0,1]]` (working note / D3b anchors) | match (`true`) |
| `uTilde 3` entrywise | `[1,3,1]` (`ũ⃗`, working note) | match (`true`) |
| brackets `c′_k = ũ⃗ N′^k 1⃗`, `n = 3`, `k = 0..3`, list side | `[5, 7, 3, 0]` — `c′_0 = \|S_3\| = 5`; `c′_2 = C(3,2)·C(3,3) = 3` (`cpBracket_top`); `c′_3 = 0` (`cpBracket_eq_zero_of_ge`, `k = n`) | `[5, 7, 3, 0]` |
| expansion `Σ_k C(r,k) c′_k`, `n = 3`, `r = 0..3` gaps | `[5, 12, 22, 35]` (ranks 1–4; D3b anchors / manuscript `(3/2)r'² + (5/2)r' + 1`) | `[5, 12, 22, 35]` |
| second difference of the above | `[3, 3]` — degree exactly `2 = n − 1`, leading coeff `3/2! = 3/2 = (C(3,2)·C(3,3))/(3−1)!`, the claim of `eq:delta0-leading` | `[3, 3]` (from `[7, 10, 13]`) |
| `NBmat 2` entrywise (formal) | `[[0,1],[0,0]]` | `[[0, 1], [0, 0]]` |
| `cpBracket 2 k`, `k = 0..2` (formal) | `[2, 1, 0]` — `c′_1 = C(2,2) = 1`, vanish at `k = n = 2` | `[2, 1, 0]` |
| expansion `Σ_k C(r,k)·cpBracket 2 k`, `r = 0..3` (formal ℚ) | `[2, 3, 4, 5]` | `[2, 3, 4, 5]` |
| `(properChainedTuples 2 (r+1) 0).card`, `r = 0..3` (formal Finset) | `[2, 3, 4, 5]` (`\|FF_pr(2;0^rank)\| = rank + 1`, degree `1 = n − 1`, leading coeff `1 = C(2,2)/1!`) | `[2, 3, 4, 5]` |
| `cpBracket 1 k`, `k = 0..1` (formal) | `[1, 0]` — the `n = 1` degenerate case: `1×1` block, `N′ = 0` | `[1, 0]` |
| `uTilde 1 ⟨0,_⟩` (formal) | `1` (**`u′[1] = 1`**, `uTilde_zero` — the load-bearing input) | `1` |
| `(properChainedTuples 1 (r+1) 0).card`, `r = 0..2` | `[1, 1, 1]` — constant `1 = \|S_1\|`, degree `0 = n − 1` (working note's parenthetical) | `[1, 1, 1]` |

Consistency notes: at `n = 2` the *formal* expansion (ℚ-valued
brackets through `cpBracket`) and the *formal* Finset count agree at
all four ranks — the two ends of
`cast_card_properChainedTuples_of_gaps_eq_zero` checked against each
other numerically as well as by proof.  The `n = 3` second difference
`3` is the entrywise witness for the leading coefficient `3/2` claimed
by the second half of `eq:delta0-leading` at `n = 3`.

## The scratch file as run

```lean
-- Scratch anchor file for rung D3d (deleted after the run, per convention).
-- Entrywise anchors, not totals.  Run: cd LEAN && lake env lean D3dCheck.lean
import ExteriorConvex.Counting.ProperDegree

open Finset Matrix ExteriorConvex

-- ## n = 3: read the formal entries ONCE each (Amat recomputes Fn n per
-- call — matrix arithmetic must never run on the formal values at n = 3).
-- Expected: B = [[1,3,1],[0,1,1],[0,0,1]], ũ = [1,3,1] (working note / D3b anchors).
#eval ((List.finRange 3).map fun i => (List.finRange 3).map fun j =>
  (Bmat 3 i j : Int)) == [[1,3,1],[0,1,1],[0,0,1]]
#eval ((List.finRange 3).map fun i => (uTilde 3 i : Int)) == [1,3,1]

-- ## n = 3, list side (independent re-implementation over List Int,
-- using the entries just verified): brackets c′_k = ũ N′^k 1 and the
-- binomial expansion sums Σ_k C(r,k) c′_k.
def nL : List (List Int) := [[0,3,1],[0,0,1],[0,0,0]]  -- B − I from above
def uL : List Int := [1,3,1]
def vmulL (v : List Int) (M : List (List Int)) : List Int :=
  (List.range 3).map fun j =>
    ((List.range 3).map fun i =>
      (v.getD i 0) * ((M.getD i []).getD j 0)).foldl (·+·) 0
def bracketsL : List Int := (List.range 4).map fun k =>
  ((List.range k).foldl (fun v _ => vmulL v nL) uL).foldl (·+·) 0
-- Expected [5, 7, 3, 0]: c′_2 = C(3,2)·C(3,3) = 3, vanishing at k = 3 = n.
#eval bracketsL
-- Expected [5, 12, 22, 35] (D3b anchors / manuscript (3/2)r'^2+(5/2)r'+1 at
-- ranks 1–4; second difference 3 = 2!·(3/2), the claimed leading coeff).
#eval (List.range 4).map fun r =>
  ((List.range 4).map fun k =>
    (Nat.choose r k : Int) * bracketsL.getD k 0).foldl (·+·) 0

-- ## n = 2, fully formal (small enough): brackets and NBmat entrywise.
-- Expected N′ = [[0,1],[0,0]]; (c′_0, c′_1, c′_2) = (2, 1, 0).
#eval (List.finRange 2).map fun i => (List.finRange 2).map fun j => NBmat 2 i j
#eval (List.range 3).map fun k => cpBracket 2 k
-- Expansion at n = 2 vs the formal Finset count, ranks 1..4.
-- Expected both [2, 3, 4, 5] (= |FF_pr(2;0^rank)| = rank + 1).
#eval (List.range 4).map fun r =>
  ((List.range 3).map fun k =>
    (Nat.choose r k : ℚ) * cpBracket 2 k).foldl (·+·) 0
#eval (List.range 4).map fun r =>
  (properChainedTuples 2 (r + 1) (fun _ => 0)).card

-- ## n = 1, the degenerate boundary: block 1×1, N′ = 0, c′_0 = 1 = ũ[0],
-- count constant 1 = |S_1|, degree 0 = n − 1.
#eval (List.range 2).map fun k => cpBracket 1 k   -- expected [1, 0]
#eval uTilde 1 ⟨0, Nat.one_pos⟩                    -- expected 1  (u′[1] = 1)
#eval (List.range 3).map fun r =>
  (properChainedTuples 1 (r + 1) (fun _ => 0)).card  -- expected [1, 1, 1]
```

Raw output of the run (after `lake build ExteriorConvex.Counting.ProperDegree`):

```
true
true
[5, 7, 3, 0]
[5, 12, 22, 35]
[[0, 1], [0, 0]]
[2, 1, 0]
[2, 3, 4, 5]
[2, 3, 4, 5]
[1, 0]
1
[1, 1, 1]
```
