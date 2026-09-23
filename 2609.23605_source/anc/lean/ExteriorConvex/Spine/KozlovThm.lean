/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 3 of the §§4–6 formalisation: Kozlov's theorem

Formalisation of `thm-kozlov` (Kozlov 1997, Theorem 4.1) from
`article/exterior-convex_article1_latest.org`, per
`working-notes/PLAN-formalise-rungs-1-4.org`, in the degree-0-inclusive
space; the file is `Kozlov1` because `Kozlov.lean` (the §8 extremal-matrix
layer, in the dropped space) is taken.

* `kozlov`: `conv(S_n) = conv{F̃_1,…,F̃_n}`, both hulls inclusive.
  The `⊆` inclusion is properness (`fEntry_one`) + local LYM (`lym`) +
  `convexHull_min` into the chain set of rung 2; the `⊇` inclusion exhibits
  each skeleton point as the `f`-vector of the complete `j`-skeleton
  `skelComplex n j`.
* `hull_Sset_eq` is `cor-facets` read inclusively: `Koz(n) = conv(S_n)`
  (`def-kozsimplex`) is cut out by `x₀ = 1`, `x₁ = n`, the LYM chain, and
  `x_n ≥ 0`.  The manuscript's `cor-facets` states this for `proj(Koz(n))`
  in the dropped space and adds that the `n` inequalities are exactly the
  facets; the projection is the out-of-scope seam (see `projIncl` in
  `Complexes.lean`), and the facet clause is dimension talk resting on
  `lem-mu`'s unformalised affine-independence clause, so **neither is
  formalised** — what is proved is the hyperplane/half-space description
  itself.
-/
import Mathlib
import ExteriorConvex.Spine.Complexes
import ExteriorConvex.Spine.LYM

open Finset

namespace ExteriorConvex

variable {n : ℕ}

/-! ## The `⊆` direction: `f`-vectors satisfy the chain -/

/-- The `f`-vector of a simplicial complex satisfies the chain description:
`x₀ = 1` (non-emptiness), `x₁ = n` (properness), the LYM chain (`lem-lym`),
and `x_n ≥ 0` (a cardinality).  This is the `⊆` computation in
`thm-kozlov`'s proof. -/
theorem Sset_subset_lymChain (hn : 1 ≤ n) : Sset n ⊆ lymChain n := by
  rintro _ ⟨D, hD, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (fEntry D (0 : Fin (n + 1)).val : ℝ) = 1
    rw [Fin.val_zero, fEntry_zero hD.ideal hD.nonempty, Nat.cast_one]
  · rw [fin_one_eq hn]
    show (fEntry D 1 : ℝ) = (n : ℝ)
    rw [fEntry_one hD]
  · intro j hj hjn
    exact lym hD.ideal hj hjn
  · exact Nat.cast_nonneg _

/-! ## The `⊇` direction: each skeleton is achieved -/

/-- The complete `j`-skeleton on `[n]`: all subsets of `[n]` of cardinality
at most `j`.  (`thm-kozlov`'s proof: "each `F̃_j` is itself the `f`-vector of
the complete `j`-skeleton".) -/
def skelComplex (n j : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun s => #s ≤ j)

/-- The complete `j`-skeleton is a simplicial complex for `j ≥ 1`. -/
theorem isComplex_skelComplex {j : ℕ} (hj : 1 ≤ j) :
    IsComplex (skelComplex n j) where
  ideal := by
    intro s t hs hts
    rw [skelComplex, mem_filter] at hs ⊢
    exact ⟨mem_univ t, le_trans (card_le_card hts) hs.2⟩
  empty_mem := by
    rw [skelComplex, mem_filter]
    simp
  singleton_mem := by
    intro i
    rw [skelComplex, mem_filter]
    simpa using hj

/-- Face counts of the complete `j`-skeleton, below the cutoff. -/
theorem fEntry_skelComplex_of_le {j k : ℕ} (hk : k ≤ j) :
    fEntry (skelComplex n j) k = n.choose k := by
  rw [fEntry]
  have hfilter : (skelComplex n j).filter (fun s => #s = k) =
      Finset.univ.powersetCard k := by
    ext s
    simp only [skelComplex, mem_filter, mem_univ, true_and, mem_powersetCard,
      filter_filter]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨subset_univ s, h⟩
    · rintro ⟨-, h⟩
      omega
  rw [hfilter, card_powersetCard, card_univ, Fintype.card_fin]

/-- Face counts of the complete `j`-skeleton, above the cutoff. -/
theorem fEntry_skelComplex_of_gt {j k : ℕ} (hk : j < k) :
    fEntry (skelComplex n j) k = 0 := by
  rw [fEntry, card_eq_zero, filter_eq_empty_iff]
  intro s hs
  rw [skelComplex, mem_filter] at hs
  omega

/-- The `f`-vector of the complete `j`-skeleton is the skeleton point
`skel n j` of `eq:skeleton`.  (True for `j = 0` as well: both sides are
`e₀`, cf. `rem-properness`.) -/
theorem fvec_skelComplex (j : ℕ) :
    fvec (skelComplex n j) = skel n j := by
  funext i
  show (fEntry (skelComplex n j) i.val : ℝ) = skel n j i
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · rw [h0, fEntry_skelComplex_of_le (Nat.zero_le j), Nat.choose_zero_right]
    simp [skel, h0]
  · by_cases hij : i.val ≤ j
    · rw [fEntry_skelComplex_of_le hij]
      simp only [skel]
      rw [ite_eq_right (by omega), ite_eq_left hij]
    · rw [fEntry_skelComplex_of_gt (by omega)]
      simp only [skel]
      rw [ite_eq_right (by omega), ite_eq_right hij, Nat.cast_zero]

/-- Every skeleton point is an achieved `f`-vector: `skelSet n ⊆ S_n`. -/
theorem skelSet_subset_Sset : skelSet n ⊆ Sset n := by
  rintro _ ⟨j, hj, rfl⟩
  rw [Set.mem_Icc] at hj
  exact ⟨skelComplex n j, isComplex_skelComplex hj.1, fvec_skelComplex j⟩

/-! ## Kozlov's theorem -/

/-- `thm-kozlov` (Kozlov 1997, Theorem 4.1), in the degree-0-inclusive
space: the convex hull of the `f`-vectors of the simplicial complexes on
`[n]` is the convex hull of the `n` skeleton points.  (The manuscript's
"an `(n−1)`-dimensional simplex" clause rests on `lem-mu`'s
affine-independence clause and is not formalised — see `LYM.lean`.) -/
theorem kozlov (hn : 1 ≤ n) :
    convexHull ℝ (Sset n) = convexHull ℝ (skelSet n) := by
  apply Set.Subset.antisymm
  · rw [hull_skel_eq hn]
    exact convexHull_min (Sset_subset_lymChain hn) (convex_lymChain n)
  · exact convexHull_mono skelSet_subset_Sset

/-- `cor-facets`, read in the inclusive space (and `def-kozsimplex`):
the Kozlov simplex `Koz(n) = conv(S_n)` is exactly the chain set —
`x₀ = 1`, `x₁ = n`, `x_j/C(n,j) ≥ x_{j+1}/C(n,j+1)` for `1 ≤ j ≤ n−1`,
`x_n ≥ 0`.  See the file header for what of `cor-facets` this does *not*
carry (the projection to `ℝ^n`, and the "exactly the facets" clause). -/
theorem hull_Sset_eq (hn : 1 ≤ n) :
    convexHull ℝ (Sset n) = lymChain n := by
  rw [kozlov hn, hull_skel_eq hn]

end ExteriorConvex
