# Rung D2 Lean numerical anchors — 2026-09-17 (jts-pc)

Sanity anchors for `LEAN/ExteriorConvex/Counting/Delta0.lean` (rung D2:
`prop-delta0` + improper half of `thm-delta0-degrees`), run during
development via a scratch file `LEAN/Delta0Check.lean` (deleted after the
run, per the rung convention that `#eval`s stay out of the formal
development; reproduce by recreating the file below and running
`cd LEAN && lake env lean Delta0Check.lean`).

Two independent computations were compared:

1. a **list-side re-implementation** of the matrix algebra (`Tn`, `un`,
   `matSub`, `vecMulL` over `List ℤ`), touching the formal development
   only through the raw entries `Tmat n 0 i j` and `uVec n k`;
2. the **formal ℚ-side definitions themselves** (`cBracket`, and the
   honest `Finset` counts `(chainedTuples n r (fun _ => 0)).card`).

## Expected vs. observed — all match

| quantity | expected (source) | observed |
|---|---|---|
| `T(0)` at `n=2` | unitriangular, superdiag `(1,2,1)` | `[[1,1,2,1],[0,1,2,1],[0,0,1,1],[0,0,0,1]]` |
| `u⃗` at `n=2` | `(1,1,2,1)` | `[1,1,2,1]` |
| brackets `c₀..c₄`, `n=2`, list side | `(5,9,7,2)` then `0` (working note §Remarks) | `[5,9,7,2,0]` |
| brackets via formal `cBracket 2 k` | same | `[5,9,7,2,0]` |
| counts at `0..4` gaps, `n=2` | `5, 14, 30, 55, 91` (manuscript `rem-delta0-degrees`: `14,30,55,91` at `r=2..5`) | `[5,14,30,55,91]` |
| `(chainedTuples 2 2 0).card` | `14` | `14` |
| `(chainedTuples 2 3 0).card` | `30` | `30` |
| `T(0)` at `n=3` | `ex-uT`'s printed matrix | `[[1,1,3,4,1],[0,1,3,4,1],[0,0,1,3,1],[0,0,0,1,1],[0,0,0,0,1]]` |
| `u⃗` at `n=3` | `(1,1,3,4,1)` (`ex-uT`) | `[1,1,3,4,1]` |
| brackets `c₀..c₅`, `n=3` | `c₄ = 9 = 1·3·3·1`, `c₅ = 0` | `[10,33,49,34,9,0]` |
| counts at `0..3` gaps, `n=3` | `10, 43, …` (`|FF(3;0,0)| = 43`) | `[10,43,125,290]` |
| `(chainedTuples 3 2 0).card` | `43` | `43` |

Consistency of the expansion `count(r gaps) = ∑ₖ C(r,k)cₖ` on the
observed values: `n=3`, `r=2`: `10 + 2·33 + 49 = 125` ✓; `r=3`:
`10 + 99 + 147 + 34 = 290` ✓.

## The scratch file (verbatim)

```lean
import ExteriorConvex.Counting.Delta0

open ExteriorConvex

namespace Delta0Check

def Tn (n : ℕ) : List (List ℤ) :=
  (List.finRange (n + 2)).map fun i =>
    (List.finRange (n + 2)).map fun j => ((Tmat n 0 i j : ℕ) : ℤ)

def un (n : ℕ) : List ℤ :=
  (List.finRange (n + 2)).map fun k => ((uVec n k : ℕ) : ℤ)

def idm (m : ℕ) : List (List ℤ) :=
  (List.range m).map fun i =>
    (List.range m).map fun j => if i = j then 1 else 0

def matSub (A B : List (List ℤ)) : List (List ℤ) :=
  A.zipWith (fun ra rb => ra.zipWith (· - ·) rb) B

def vecMulL (v : List ℤ) (M : List (List ℤ)) : List ℤ :=
  match M with
  | [] => []
  | r0 :: _ =>
    (List.range r0.length).map fun j =>
      ((v.zip M).map fun p => p.1 * (p.2.getD j 0)).sum

def iterVecMul (v : List ℤ) (M : List (List ℤ)) : ℕ → List ℤ
  | 0 => v
  | k + 1 => vecMulL (iterVecMul v M k) M

def brackets (n : ℕ) : List ℤ :=
  let N := matSub (Tn n) (idm (n + 2))
  (List.range (n + 3)).map fun k => (iterVecMul (un n) N k).sum

def countL (n r : ℕ) : ℤ := (iterVecMul (un n) (Tn n) r).sum

end Delta0Check

open Delta0Check

#eval Tn 2
#eval un 2
#eval brackets 2
#eval (List.range 5).map (countL 2)
#eval (List.range 5).map fun k => cBracket 2 k
#eval (chainedTuples 2 2 (fun _ => 0)).card
#eval (chainedTuples 2 3 (fun _ => 0)).card
#eval Tn 3
#eval un 3
#eval brackets 3
#eval (List.range 4).map (countL 3)
#eval (chainedTuples 3 2 (fun _ => 0)).card
```
