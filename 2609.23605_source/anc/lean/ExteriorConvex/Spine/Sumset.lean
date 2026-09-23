/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 4 of the §§4–6 formalisation: the sumset identity and the main theorem

Formalisation of `def-ffvector`, `prop-sumset` and `thm-main` from
`article/exterior-convex_article1_latest.org`, per
`working-notes/PLAN-formalise-rungs-1-4.org`.

* `ffvec` is `eq:ffvector`: `ff(Δ⃗)_j = ∑_i f_{j−d_i}(Δ_i)`, with `f`
  extended by `0` below `0` (the guard `d i ≤ j`) and above `n`
  (`fEntry_eq_zero_of_lt`, no guard needed).
* `ff_eq_sumset` is `prop-sumset`'s second equality: the set of achievable
  `ff`-vectors is the Minkowski sum `∑_i shift^{d_i}(S_n)`.  (The *first*
  equality of `prop-sumset` — Hilbert functions of proper monomial
  submodules = `ff`-vectors — is the algebraic dictionary
  `prop-splitting`/`prop-dictionary` and is not in rungs 1–4's scope;
  the combinatorial side is taken as the definition here.)
* `main` is `thm-main` in its "equivalently, by `prop-sumset`" form:
  `conv(ffSet) = ∑_i shift^{d_i}(conv(S_n))`, via `convexHull_sum` and
  `LinearMap.image_convexHull`; `main_chain` composes it with rung 3's
  `hull_Sset_eq` to make each summand the explicit chain polytope.

**A finding, mild but worth recording**: the manuscript states `thm-main`
and `prop-sumset` under `n ≥ 1`, `r ≥ 1`, `0 = d_1 ≤ ⋯ ≤ d_r`, `N = n + d_r`.
None of these hypotheses is needed for the identities formalised here, and
the Lean statements carry none of them (`n`, `N`, `r`, `d` are arbitrary;
if `N < n + d_i` both sides truncate identically).  The manuscript itself
half-says this after `prop-sumset` ("nothing here uses … any property of
`S_n` beyond its being some fixed finite subset").  The hypotheses do
matter elsewhere (`thm-kozlov` needs `n ≥ 1`, §8 needs the ordering), just
not for these two statements.
-/
import Mathlib
import ExteriorConvex.Spine.Complexes
import ExteriorConvex.Spine.KozlovThm

open Finset
open scoped Pointwise

namespace ExteriorConvex

variable {n N : ℕ} {r : ℕ}

/-- `def-ffvector` / `eq:ffvector`: the `ff`-vector of an `r`-vector of
complexes `Δ⃗ = (Δ_1, …, Δ_r)` with respect to the shift vector `d`, as a
point of the inclusive space `Fin (N+1) → ℝ`:
`ff(Δ⃗)_j = ∑_i f_{j−d_i}(Δ_i)`, the summand read as `0` for `j < d_i`. -/
def ffvec (N : ℕ) (d : Fin r → ℕ) (D : Fin r → Finset (Finset (Fin n))) :
    Fin (N + 1) → ℝ := fun j =>
  ∑ i, if d i ≤ j.val then (fEntry (D i) (j.val - d i) : ℝ) else 0

/-- The set of achievable `ff`-vectors: `{ff(Δ⃗) : Δ⃗ an r-vector on [n]}`
(`prop-sumset`, left-hand side of `eq:sumset`'s combinatorial half). -/
def ffSet (n N : ℕ) (d : Fin r → ℕ) : Set (Fin (N + 1) → ℝ) :=
  {x | ∃ D : Fin r → Finset (Finset (Fin n)),
    (∀ i, IsComplex (D i)) ∧ ffvec N d D = x}

/-- The coordinatewise observation in `prop-sumset`'s proof: "by
construction `shift^d(s)_j = f_{j−d}(Δ)` for *every* `j`", both sides being
zero outside `d ≤ j ≤ d + n`. -/
theorem shiftIncl_fvec (D : Finset (Finset (Fin n))) (d : ℕ)
    (j : Fin (N + 1)) :
    shiftIncl N d (fvec D) j =
      if d ≤ j.val then (fEntry D (j.val - d) : ℝ) else 0 := by
  rw [shiftIncl_apply]
  by_cases h1 : d ≤ j.val ∧ j.val - d ≤ n
  · rw [dite_eq_left h1, ite_eq_left h1.1]
    rfl
  · rw [dite_eq_right h1]
    by_cases h2 : d ≤ j.val
    · rw [ite_eq_left h2, fEntry_eq_zero_of_lt (by omega), Nat.cast_zero]
    · rw [ite_eq_right h2]

/-- The `ff`-vector is the sum of the shifted `f`-vectors:
`ff(Δ⃗) = ∑_i shift^{d_i}(f(Δ_i))` as points of `ℝ^{N+1}`. -/
theorem ffvec_eq_sum_shift (d : Fin r → ℕ)
    (D : Fin r → Finset (Finset (Fin n))) :
    ffvec N d D = ∑ i, shiftIncl N (d i) (fvec (D i)) := by
  funext j
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (shiftIncl_fvec (D i) (d i) j).symm

/-- `prop-sumset` (the combinatorial equality of `eq:sumset` with
`eq:sumset-2`): the achievable set is exactly the Minkowski sum
`∑_i shift^{d_i}(S_n)`, one summand per generator degree, repeated degrees
contributing repeated summands.  Choosing the `Δ_i` independently *is*
forming the sumset. -/
theorem ff_eq_sumset (n N : ℕ) (d : Fin r → ℕ) :
    ffSet n N d = ∑ i, shiftIncl N (d i) '' Sset n := by
  ext x
  constructor
  · rintro ⟨D, hD, rfl⟩
    rw [ffvec_eq_sum_shift]
    exact Set.finsetSum_mem_finsetSum Finset.univ _ _
      (fun i _ => Set.mem_image_of_mem _ ⟨D i, hD i, rfl⟩)
  · intro hx
    rw [Set.mem_fintype_sum] at hx
    obtain ⟨g, hg, hsum⟩ := hx
    have h : ∀ i, ∃ Di : Finset (Finset (Fin n)),
        IsComplex Di ∧ shiftIncl N (d i) (fvec Di) = g i := by
      intro i
      obtain ⟨y, hy, hgy⟩ := hg i
      obtain ⟨Di, hDi, rfl⟩ := hy
      exact ⟨Di, hDi, hgy⟩
    choose D hDc hDg using h
    refine ⟨D, hDc, ?_⟩
    rw [ffvec_eq_sum_shift, ← hsum]
    exact Finset.sum_congr rfl fun i _ => hDg i

/-- `thm-main`, in its "equivalently, by `prop-sumset`" form: the convex
hull of the achievable `ff`-vectors is the Minkowski sum of `r` shifted
copies of `conv(S_n)` — one and the same Kozlov simplex (`kozlov`,
`def-kozsimplex`), one copy per generator degree.
`Koz(n; d_1, …, d_r)` is the right-hand side.

The proof is the manuscript's: `prop-sumset`, then hull-commutes-with-sum
(`convexHull_sum`, the manuscript's `lem-convex`(A) iterated), then
hull-commutes-with-linear-images (`LinearMap.image_convexHull`,
`lem-convex`(B)) applied to each `shift^{d_i}`. -/
theorem main (n N : ℕ) (d : Fin r → ℕ) :
    convexHull ℝ (ffSet n N d) =
      ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n) := by
  rw [ff_eq_sumset, convexHull_sum]
  exact Finset.sum_congr rfl
    fun i _ => ((shiftIncl N (d i)).image_convexHull (Sset n)).symm

/-- `thm-main` combined with `cor-facets` (`hull_Sset_eq`): for `n ≥ 1`,
each summand is the explicit chain polytope, so the Kozlov polytope is the
Minkowski sum of `r` shifted copies of the chain set. -/
theorem main_chain (hn : 1 ≤ n) (N : ℕ) (d : Fin r → ℕ) :
    convexHull ℝ (ffSet n N d) =
      ∑ i, shiftIncl N (d i) '' lymChain n := by
  rw [main n N d]
  exact Finset.sum_congr rfl fun i _ => by rw [hull_Sset_eq hn]

end ExteriorConvex
