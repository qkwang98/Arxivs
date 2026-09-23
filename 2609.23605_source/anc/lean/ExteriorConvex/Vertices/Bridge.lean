/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 1: the bridge lemma

Formalisation of §8's `lem-exposed-vertex` and `lem-vertexdecomp` from
`article/exterior-convex_article1_latest.org`.

The point of this file is recorded in `working-notes/formalization-bridge-lemma.org`: Mathlib has no
polytope, but §8.2-8.4 never needs one.  Every body there is `convexHull ℝ S` for an explicit finite
`S`, and "vertex" is `Set.extremePoints ℝ`.  These two lemmas replace the word "vertex" by the
existence of a linear functional with a unique maximiser over a finite set, after which every
statement in §8 is a finite system of strict linear inequalities.

Note that `mem_extremePoints_add_iff` is proved here WITHOUT support-function additivity (the
manuscript cites Ziegler, Proposition 7.12): passing through `convexHull_add` reduces the Minkowski
statement to the single-polytope one, and the rest is a two-line exchange argument.
-/
import Mathlib

open Set Pointwise

namespace ExteriorConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear functional that is uniquely maximised at `x` over `S` is uniquely maximised at `x`
over `convexHull ℝ S`.  This is the analytic content of the easy direction, isolated because both
theorems below use it. -/
theorem lt_of_mem_convexHull {S : Set E} {x : E} {f : E →L[ℝ] ℝ}
    (hxS : x ∈ S) (hf : ∀ y ∈ S, y ≠ x → f y < f x) :
    ∀ y ∈ convexHull ℝ S, y ≠ x → f y < f x := by
  rcases eq_or_ne (S \ {x}) ∅ with hempty | hne
  · -- `S = {x}`: the hull is a single point and the claim is vacuous.
    have hSx : S = {x} :=
      Subset.antisymm (sdiff_eq_empty.mp hempty) (singleton_subset_iff.mpr hxS)
    subst hSx
    simp
  · have hTne : (S \ {x}).Nonempty := nonempty_iff_ne_empty.mpr hne
    -- The other generators, and hence their hull, lie strictly below `f x`.
    have hTlt : convexHull ℝ (S \ {x}) ⊆ {z | f z < f x} :=
      convexHull_min (fun y hy => hf y hy.1 hy.2)
        (convex_halfSpace_lt f.toLinearMap.isLinear _)
    intro y hy hyx
    have hSins : S = insert x (S \ {x}) := by
      rw [insert_sdiff_singleton, insert_eq_self.mpr hxS]
    rw [hSins, convexHull_insert hTne] at hy
    obtain ⟨a, ha, b, hb, hseg⟩ := mem_convexJoin.mp hy
    rw [mem_singleton_iff] at ha
    subst ha
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hseg
    have hfb : f b < f a := hTlt hb
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [show u = 1 by linarith] at hyx
      simp at hyx
    have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    have hval : f (u • a + v • b) = f a - v * (f a - f b) := by
      have hu1 : u = 1 - v := by linarith
      simp only [map_add, map_smul, smul_eq_mul, hu1]
      ring
    rw [hval]
    have := mul_pos hvpos (sub_pos.mpr hfb)
    linarith

/-- **The bridge lemma** (`lem-exposed-vertex`).  For a finite generating set, being a vertex of the
convex hull is the same as being the unique maximiser of some linear functional over the
generators. -/
theorem mem_extremePoints_convexHull_iff {S : Set E} (hS : S.Finite) (x : E) :
    x ∈ Set.extremePoints ℝ (convexHull ℝ S) ↔
      x ∈ S ∧ ∃ f : E →L[ℝ] ℝ, ∀ y ∈ S, y ≠ x → f y < f x := by
  constructor
  · intro hx
    have hxS : x ∈ S := extremePoints_convexHull_subset hx
    refine ⟨hxS, ?_⟩
    -- `x` is not in the hull of the other generators.
    have hnot : x ∉ convexHull ℝ (S \ {x}) := by
      have h := (convex_convexHull ℝ S).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp hx
      have hmono : convexHull ℝ (S \ {x}) ⊆ convexHull ℝ (convexHull ℝ S \ {x}) :=
        convexHull_mono (fun y hy => ⟨subset_convexHull ℝ S hy.1, hy.2⟩)
      exact fun hmem => h.2 (hmono hmem)
    -- Separate it from that hull, which is closed and convex.
    have hfin : (S \ {x}).Finite := hS.sdiff
    have hclosed : IsClosed (convexHull ℝ (S \ {x})) := Set.Finite.isClosed_convexHull ℝ hfin
    obtain ⟨f, u, hlt, hgt⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ (S \ {x})) hclosed hnot
    exact ⟨f, fun y hy hne => lt_trans (hlt y (subset_convexHull ℝ _ ⟨hy, hne⟩)) hgt⟩
  · rintro ⟨hxS, f, hf⟩
    have hstrict := lt_of_mem_convexHull hxS hf
    rw [(convex_convexHull ℝ S).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff]
    refine ⟨subset_convexHull ℝ S hxS, fun hmem => ?_⟩
    have hsub : convexHull ℝ (convexHull ℝ S \ {x}) ⊆ {z | f z < f x} :=
      convexHull_min (fun y hy => hstrict y hy.1 hy.2)
        (convex_halfSpace_lt f.toLinearMap.isLinear _)
    have hcontra := hsub hmem
    simp only [mem_ofPred_eq] at hcontra
    exact lt_irrefl _ hcontra

/-- **The Minkowski decomposition lemma** (`lem-vertexdecomp`), for polytopes presented by finite
generating sets.  A sum of generators is a vertex of the Minkowski sum exactly when a *single*
functional has each summand as its unique maximiser. -/
theorem mem_extremePoints_add_iff {S T : Set E} (hS : S.Finite) (hT : T.Finite)
    {s t : E} (hs : s ∈ S) (ht : t ∈ T) :
    s + t ∈ Set.extremePoints ℝ (convexHull ℝ S + convexHull ℝ T) ↔
      ∃ f : E →L[ℝ] ℝ, (∀ y ∈ S, y ≠ s → f y < f s) ∧ (∀ y ∈ T, y ≠ t → f y < f t) := by
  rw [← convexHull_add, mem_extremePoints_convexHull_iff (hS.add hT)]
  constructor
  · rintro ⟨-, f, hf⟩
    refine ⟨f, fun y hy hne => ?_, fun y hy hne => ?_⟩
    · -- Exchange argument: swap `s` for a competitor and compare inside the sumset.
      have hmem : y + t ∈ S + T := ⟨y, hy, t, ht, rfl⟩
      have hne' : y + t ≠ s + t := fun h => hne (add_right_cancel h)
      have := hf _ hmem hne'
      simp only [map_add] at this
      linarith
    · have hmem : s + y ∈ S + T := ⟨s, hs, y, hy, rfl⟩
      have hne' : s + y ≠ s + t := fun h => hne (add_left_cancel h)
      have := hf _ hmem hne'
      simp only [map_add] at this
      linarith
  · rintro ⟨f, hfs, hft⟩
    refine ⟨⟨s, hs, t, ht, rfl⟩, f, ?_⟩
    rintro z ⟨y, hy, w, hw, rfl⟩ hne
    have hsplit : y ≠ s ∨ w ≠ t := by
      by_contra hc
      push Not at hc
      exact hne (by rw [hc.1, hc.2])
    have h1 : f y ≤ f s := by
      rcases eq_or_ne y s with rfl | h
      · exact le_refl _
      · exact (hfs y hy h).le
    have h2 : f w ≤ f t := by
      rcases eq_or_ne w t with rfl | h
      · exact le_refl _
      · exact (hft w hw h).le
    simp only [map_add]
    rcases hsplit with h | h
    · have := hfs y hy h; linarith
    · have := hft w hw h; linarith

/-- **A vertex of a Minkowski sum decomposes in exactly one way.**  This is the uniqueness half of
`lem-vertexdecomp`, isolated because the vertex *count* needs it: it is what makes
`(i,j) ↦ v_i + u_j` injective on the pairs that survive. -/
theorem eq_of_add_eq_of_mem_extremePoints {S T : Set E} {x s s' t t' : E}
    (hx : x ∈ Set.extremePoints ℝ (convexHull ℝ S + convexHull ℝ T))
    (hs : s ∈ convexHull ℝ S) (ht : t ∈ convexHull ℝ T)
    (hs' : s' ∈ convexHull ℝ S) (ht' : t' ∈ convexHull ℝ T)
    (h1 : s + t = x) (h2 : s' + t' = x) : s = s' ∧ t = t' := by
  subst h1
  -- The two "crossed" points also lie in the sum, and `x` is their midpoint.
  have hy : s + t' ∈ convexHull ℝ S + convexHull ℝ T := ⟨s, hs, t', ht', rfl⟩
  have hz : s' + t ∈ convexHull ℝ S + convexHull ℝ T := ⟨s', hs', t, ht, rfl⟩
  have key : (s + t') + (s' + t) = (s + t) + (s + t) := by
    calc (s + t') + (s' + t) = (s' + t') + (s + t) := by abel
      _ = (s + t) + (s + t) := by rw [h2]
  have hmid : (2⁻¹ : ℝ) • (s + t') + (2⁻¹ : ℝ) • (s' + t) = s + t := by
    rw [← smul_add, key, ← two_smul ℝ (s + t), smul_smul]
    norm_num
  have hseg : (s + t) ∈ openSegment ℝ (s + t') (s' + t) :=
    ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, hmid⟩
  have hyx : s + t' = s + t := (mem_extremePoints_iff_left.mp hx).2 _ hy _ hz hseg
  have htt : t' = t := add_left_cancel hyx
  subst htt
  exact ⟨(add_right_cancel h2).symm, rfl⟩

/-- **A vertex decomposes only through the generating sets.**  Together with
`eq_of_add_eq_of_mem_extremePoints` this is what lets the manuscript state `lem-vertexdecomp`(1)
for arbitrary `x_p ∈ P_p` rather than only for `x_p` in the generating sets: a vertex has one
decomposition, and that decomposition is by generators. -/
theorem mem_of_add_eq_of_mem_extremePoints {S T : Set E} {x s t : E}
    (hx : x ∈ Set.extremePoints ℝ (convexHull ℝ S + convexHull ℝ T))
    (hs : s ∈ convexHull ℝ S) (ht : t ∈ convexHull ℝ T) (h : s + t = x) :
    s ∈ S ∧ t ∈ T := by
  have hx' : x ∈ Set.extremePoints ℝ (convexHull ℝ (S + T)) := by rwa [convexHull_add]
  obtain ⟨s', hs', t', ht', hst⟩ := extremePoints_convexHull_subset hx'
  obtain ⟨e1, e2⟩ := eq_of_add_eq_of_mem_extremePoints hx hs ht
    (subset_convexHull ℝ S hs') (subset_convexHull ℝ T ht') h hst
  exact ⟨e1 ▸ hs', e2 ▸ ht'⟩

end ExteriorConvex
