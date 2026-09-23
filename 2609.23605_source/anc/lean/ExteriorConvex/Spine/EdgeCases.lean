/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# After the rungs: the formalisable parts of `prop-edge-cases`

The corollaries of `working-notes/PLAN-formalise-rungs-1-4.org`'s "Then,
and only then" section: parts 1 and 3 of `prop-edge-cases` from
`article/exterior-convex_article1_latest.org`.

Of the proposition's five parts, exactly two are formalisable tonight, and
that count is itself the finding of the companion assessment
(`working-notes/PLAN-formalise-prop-edge-cases.org`):

* **Part 1** (`edge_case_r_one`): at `r = 1`, `d₁ = 0`, the main theorem
  *is* Kozlov's theorem — `ffSet` collapses to `S_n` (`ffSet_r_one`) and
  `shift⁰` is the identity (`shiftIncl_zero`).
* **Part 2** (tied degrees) is **not a theorem**: the hypotheses of
  `thm-main` already permit ties — in `Sumset.lean` the shift vector
  `d : Fin r → ℕ` carries no distinctness condition to remove.  Nothing to
  state; deliberately no Lean here.
* **Part 3** (`edge_case_n_one`): at `n = 1` both sides are the single
  point `∑_i shift^{d_i}(1,1)`, via `Sset_one : S₁ = {(1,1)}`.
* **Part 4** (`n = 0` excluded) is **not a theorem either**: it is the
  remark explaining why `thm-kozlov` carries `n ≥ 1` (the vertex list is
  empty at `n = 0`), which in Lean is visible as the hypothesis `hn : 1 ≤ n`
  of `kozlov` — a hypothesis, not a statement.  Deliberately no Lean here.
* **Part 5** (dropping properness) needs the permissive variant of
  Kozlov's theorem (`rem-properness`), which is rung 5 and out of tonight's
  scope.
-/
import Mathlib
import ExteriorConvex.Spine.Complexes
import ExteriorConvex.Spine.LYM
import ExteriorConvex.Spine.KozlovThm
import ExteriorConvex.Spine.Sumset

open Finset
open scoped Pointwise

namespace ExteriorConvex

variable {n N : ℕ} {r : ℕ}

/-- `shift⁰` into the same space is the identity. -/
theorem shiftIncl_zero (x : Fin (n + 1) → ℝ) : shiftIncl n 0 x = x := by
  funext j
  rw [shiftIncl_apply, dite_eq_left ⟨Nat.zero_le _, by omega⟩]
  rfl

/-- At `r = 1`, `d₁ = 0`: the achievable set is `S_n` itself. -/
theorem ffSet_r_one : ffSet n n (fun _ : Fin 1 => 0) = Sset n := by
  ext x
  constructor
  · rintro ⟨D, hD, rfl⟩
    rw [ffvec_eq_sum_shift, Fin.sum_univ_one, shiftIncl_zero]
    exact ⟨D 0, hD 0, rfl⟩
  · rintro ⟨D, hD, rfl⟩
    exact ⟨fun _ => D, fun _ => hD,
      by rw [ffvec_eq_sum_shift, Fin.sum_univ_one, shiftIncl_zero]⟩

/-- `prop-edge-cases`(1): for `r = 1` (so `d₁ = 0`, `N = n`) the main
theorem is Kozlov's theorem, with no index shift and no leftover
translation. -/
theorem edge_case_r_one (hn : 1 ≤ n) :
    convexHull ℝ (ffSet n n (fun _ : Fin 1 => 0)) =
      convexHull ℝ (skelSet n) := by
  rw [ffSet_r_one, kozlov hn]

/-- `𝒮₁` realises the single `f`-vector `(1, 1)`: `S₁ = {(1,1)}`
(`prop-edge-cases`(3)'s computation). -/
theorem Sset_one : Sset 1 = {(fun _ => 1 : Fin 2 → ℝ)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨D, hD, rfl⟩
    funext j
    show (fEntry D j.val : ℝ) = 1
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with h | h
    · rw [h, fEntry_zero hD.ideal hD.nonempty, Nat.cast_one]
    · rw [h, fEntry_one hD, Nat.cast_one]
  · rintro rfl
    have hD : IsComplex (Finset.univ : Finset (Finset (Fin 1))) :=
      ⟨fun s t _ _ => mem_univ t, mem_univ _, fun i => mem_univ _⟩
    refine ⟨Finset.univ, hD, ?_⟩
    funext j
    show (fEntry Finset.univ j.val : ℝ) = 1
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with h | h
    · rw [h, fEntry_zero hD.ideal hD.nonempty, Nat.cast_one]
    · rw [h, fEntry_one hD, Nat.cast_one]

/-- `prop-edge-cases`(3): for `n = 1` both sides of the main theorem reduce
to the single point `∑_i shift^{d_i}(1,1)`. -/
theorem edge_case_n_one (N : ℕ) (d : Fin r → ℕ) :
    convexHull ℝ (ffSet 1 N d) =
      {∑ i, shiftIncl N (d i) (fun _ => 1 : Fin 2 → ℝ)} := by
  rw [main 1 N d, Sset_one]
  have hterm : ∀ i : Fin r,
      shiftIncl N (d i) '' convexHull ℝ {(fun _ => 1 : Fin 2 → ℝ)} =
        {shiftIncl N (d i) (fun _ => 1 : Fin 2 → ℝ)} := by
    intro i
    rw [convexHull_singleton, Set.image_singleton]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact Set.finsetSum_singleton _ _

end ExteriorConvex
