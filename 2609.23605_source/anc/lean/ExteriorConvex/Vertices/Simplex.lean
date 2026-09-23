/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 2, geometric layer: `thm-ones` about the actual Minkowski sum

`Bridge.lean` turns "vertex" into "unique maximiser of a functional"; `Windows.lean` decides when two
prescribed maxima are simultaneously realisable.  This file connects them to the manuscript's
objects, for the all-ones leg vector, and states `thm-ones` about
`∠(1,…,1) + shift^d(∠(1,…,1))` itself.

The connection is one vector identity and no analysis at all.  For the all-ones leg vector the
`k`-th vertex of the summand shifted by `d` is the *indicator of the coordinate interval*
`(d, d+k]`, so

    pfx (d+k) = pfx d + rav d k

with `pfx t` the indicator of `(0,t]`.  Applying a linear functional gives
`f (rav d k) = Φ (d+k) - Φ d` with `Φ t = f (pfx t)`, which is the manuscript's passage to partial
sums -- there it is phrased as a bijection `φ ↦ Φ` onto real sequences, here as additivity of `f`.

**Index convention.**  Coordinates are `Fin N`, and `c : Fin N` stands for the manuscript's
coordinate `c.val + 1`.  Vertex indices `i`, `j`, `k` are the manuscript's own, running `1,…,n`.
-/
import Mathlib
import ExteriorConvex.Vertices.Bridge
import ExteriorConvex.Vertices.Windows

namespace ExteriorConvex

open Finset Pointwise

/-- `pfx N t` is the indicator of the manuscript's coordinates `1,…,t`: the `t`-th vertex of the
*unshifted* all-ones right-angle simplex. -/
def pfx (N t : ℕ) : Fin N → ℝ := fun c => if c.val + 1 ≤ t then 1 else 0

/-- `rav N d k` is the `k`-th vertex of the all-ones right-angle simplex shifted by `d`: the
indicator of the manuscript's coordinates `d+1,…,d+k`. -/
def rav (N d k : ℕ) : Fin N → ℝ := fun c => if d + 1 ≤ c.val + 1 ∧ c.val + 1 ≤ d + k then 1 else 0

@[simp] lemma rav_zero_shift (N k : ℕ) : rav N 0 k = pfx N k := by
  funext c
  have h : (0 + 1 ≤ c.val + 1 ∧ c.val + 1 ≤ 0 + k) ↔ (c.val + 1 ≤ k) := by omega
  simp only [rav, pfx, h]

@[simp] lemma pfx_zero (N : ℕ) : pfx N 0 = 0 := by
  funext c; simp [pfx]

/-- The identity the whole file rests on: a prefix splits as a shorter prefix plus a window. -/
lemma pfx_eq_add (N d k : ℕ) : pfx N (d + k) = pfx N d + rav N d k := by
  funext c
  simp only [pfx, rav, Pi.add_apply]
  by_cases h1 : c.val + 1 ≤ d
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; norm_num
  · by_cases h2 : c.val + 1 ≤ d + k
    · rw [if_pos h2, if_neg h1, if_pos (by omega)]; norm_num
    · rw [if_neg h2, if_neg h1, if_neg (by omega)]; norm_num

/-- Applying a linear functional to a shifted vertex gives a difference of partial sums. -/
lemma map_rav {N : ℕ} (f : (Fin N → ℝ) →L[ℝ] ℝ) (d k : ℕ) :
    f (rav N d k) = f (pfx N (d + k)) - f (pfx N d) := by
  have h := pfx_eq_add N d k
  have : f (pfx N (d + k)) = f (pfx N d) + f (rav N d k) := by rw [h, map_add]
  linarith

/-- Prefixes grow by one standard basis vector at a time. -/
lemma pfx_succ (N t : ℕ) (ht : t < N) :
    pfx N (t + 1) = pfx N t + Pi.single (⟨t, ht⟩ : Fin N) 1 := by
  funext c
  simp only [pfx, Pi.add_apply, Pi.single_apply]
  by_cases hc : c = (⟨t, ht⟩ : Fin N)
  · subst hc; simp
  · have hne : c.val ≠ t := fun h => hc (Fin.ext h)
    rw [if_neg hc, add_zero]
    by_cases h : c.val + 1 ≤ t
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

/-- The functional with prescribed coefficients. -/
noncomputable def coeffCLM {N : ℕ} (w : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (∑ c, w c • LinearMap.proj c)

lemma coeffCLM_apply {N : ℕ} (w x : Fin N → ℝ) : coeffCLM w x = ∑ c, w c * x c := by
  simp [coeffCLM, LinearMap.toContinuousLinearMap]

@[simp] lemma coeffCLM_single {N : ℕ} (w : Fin N → ℝ) (c : Fin N) :
    coeffCLM w (Pi.single c 1) = w c := by
  rw [coeffCLM_apply]
  simp [Pi.single_apply]

/-- **Every real sequence is realised by a functional**, up to the irrelevant constant `Φ 0`.
This is the manuscript's "`φ ↦ Φ` is a bijection onto real sequences", in the only direction that
needs an argument. -/
lemma exists_functional (N : ℕ) (Φ : ℕ → ℝ) :
    ∃ f : (Fin N → ℝ) →L[ℝ] ℝ, ∀ t ≤ N, f (pfx N t) = Φ t - Φ 0 := by
  refine ⟨coeffCLM (fun c => Φ (c.val + 1) - Φ c.val), ?_⟩
  intro t ht
  induction t with
  | zero => simp
  | succ s ih =>
      have hs : s < N := by omega
      rw [pfx_succ N s hs, map_add, ih (by omega), coeffCLM_single]
      simp

/-- **`thm-ones` at the level of functionals.**  Combining `Windows.thm_ones_windows` with the
passage to partial sums: the two vertices `v_i` and `u_j` are simultaneously and uniquely exposed
exactly off the manuscript's zero set. -/
theorem exists_functional_ones_iff {n d i j : ℕ} (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) :
    (∃ f : (Fin (n + d) → ℝ) →L[ℝ] ℝ,
        (∀ k ∈ Finset.Icc 1 n, k ≠ i → f (rav (n + d) 0 k) < f (rav (n + d) 0 i)) ∧
        (∀ k ∈ Finset.Icc 1 n, k ≠ j → f (rav (n + d) d k) < f (rav (n + d) d j)))
      ↔ ¬(1 ≤ i - d ∧ i - d ≤ n - d ∧ 1 ≤ j ∧ j ≤ n - d ∧ i - d ≠ j) := by
  rw [← thm_ones_windows hd hdn hi hin hj hjn]
  constructor
  · -- From a functional, take `Φ t = f (pfx t)`.
    rintro ⟨f, h₁, h₂⟩
    refine ⟨fun t => f (pfx (n + d) t), fun x hx hxi => ?_, fun x hx hxj => ?_⟩
    · simp only [Finset.mem_Icc] at hx
      have := h₁ x (Finset.mem_Icc.mpr hx) hxi
      rwa [rav_zero_shift, rav_zero_shift] at this
    · simp only [Finset.mem_Icc] at hx
      obtain ⟨k, hk⟩ : ∃ k, x = d + k := ⟨x - d, by omega⟩
      subst hk
      have hkmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr (by omega)
      have hkj : k ≠ j := fun h => hxj (by omega)
      have := h₂ k hkmem hkj
      rw [map_rav, map_rav] at this
      linarith
  · -- From a sequence, build the functional.
    rintro ⟨Φ, h₁, h₂⟩
    obtain ⟨f, hf⟩ := exists_functional (n + d) Φ
    refine ⟨f, fun k hk hki => ?_, fun k hk hkj => ?_⟩
    · simp only [Finset.mem_Icc] at hk
      rw [rav_zero_shift, rav_zero_shift, hf k (by omega), hf i (by omega)]
      have := h₁ k (Finset.mem_Icc.mpr hk) hki
      linarith
    · simp only [Finset.mem_Icc] at hk
      rw [map_rav, map_rav, hf (d + k) (by omega), hf (d + j) (by omega), hf d (by omega)]
      have := h₂ (d + k) (Finset.mem_Icc.mpr (by omega)) (by omega)
      linarith

/-- The vertex set of the summand shifted by `d`. -/
def vset (N d n : ℕ) : Set (Fin N → ℝ) := (fun k => rav N d k) '' (Set.Icc 1 n)

lemma vset_finite (N d n : ℕ) : (vset N d n).Finite := (Set.finite_Icc 1 n).image _

lemma rav_mem_vset {N d n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : rav N d k ∈ vset N d n :=
  ⟨k, ⟨hk, hkn⟩, rfl⟩

/-- The `n` vertices of a shifted summand are distinct, provided the window fits in the ambient
space.  This is what makes the extremal matrix's indices meaningful. -/
lemma rav_injOn {N d n : ℕ} (h : d + n ≤ N) : Set.InjOn (rav N d) (Set.Icc 1 n) := by
  intro k hk k' hk' hEq
  simp only [Set.mem_Icc] at hk hk'
  by_contra hne
  -- Evaluate at the last coordinate of the longer window.
  rcases Nat.lt_or_ge k k' with hlt | hge
  · have hb : d + k' - 1 < N := by omega
    have hzero : rav N d k ⟨d + k' - 1, hb⟩ = 0 := by
      simp only [rav, Fin.val_mk]; rw [if_neg]; omega
    have hone : rav N d k' ⟨d + k' - 1, hb⟩ = 1 := by
      simp only [rav, Fin.val_mk]; rw [if_pos]; omega
    rw [congrFun hEq ⟨d + k' - 1, hb⟩, hone] at hzero
    norm_num at hzero
  · have hlt : k' < k := by omega
    have hb : d + k - 1 < N := by omega
    have hone : rav N d k ⟨d + k - 1, hb⟩ = 1 := by
      simp only [rav, Fin.val_mk]; rw [if_pos]; omega
    have hzero : rav N d k' ⟨d + k - 1, hb⟩ = 0 := by
      simp only [rav, Fin.val_mk]; rw [if_neg]; omega
    rw [congrFun hEq ⟨d + k - 1, hb⟩, hzero] at hone
    norm_num at hone

/-- **`thm-ones`, geometrically.**  For the all-ones leg vector, `v_i + u_j` is a vertex of
`∠(1,…,1) + shift^d(∠(1,…,1))` exactly off the zero set `1 ≤ t ≤ m`, `1 ≤ j ≤ m`, `t ≠ j` of the
manuscript, where `t = i - d` and `m = n - d`. -/
theorem thm_ones {n d i j : ℕ} (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) :
    rav (n + d) 0 i + rav (n + d) d j ∈
        Set.extremePoints ℝ
          (convexHull ℝ (vset (n + d) 0 n) + convexHull ℝ (vset (n + d) d n))
      ↔ ¬(1 ≤ i - d ∧ i - d ≤ n - d ∧ 1 ≤ j ∧ j ≤ n - d ∧ i - d ≠ j) := by
  rw [mem_extremePoints_add_iff (vset_finite _ _ _) (vset_finite _ _ _)
      (rav_mem_vset hi hin) (rav_mem_vset hj hjn),
    ← exists_functional_ones_iff hd hdn hi hin hj hjn]
  constructor
  · -- Set form to index form: needs the vertices to be distinct.
    rintro ⟨f, hS, hT⟩
    refine ⟨f, fun k hk hki => ?_, fun k hk hkj => ?_⟩
    · simp only [Finset.mem_Icc] at hk
      refine hS _ (rav_mem_vset hk.1 hk.2) ?_
      exact fun hcontra => hki (rav_injOn (by omega) ⟨hk.1, hk.2⟩ ⟨hi, hin⟩ hcontra)
    · simp only [Finset.mem_Icc] at hk
      refine hT _ (rav_mem_vset hk.1 hk.2) ?_
      exact fun hcontra => hkj (rav_injOn (by omega) ⟨hk.1, hk.2⟩ ⟨hj, hjn⟩ hcontra)
  · -- Index form to set form: no injectivity needed.
    rintro ⟨f, hS, hT⟩
    refine ⟨f, ?_, ?_⟩
    · rintro y ⟨k, hk, rfl⟩ hne
      exact hS k (Finset.mem_Icc.mpr hk) (fun hcontra => hne (by rw [hcontra]))
    · rintro y ⟨k, hk, rfl⟩ hne
      exact hT k (Finset.mem_Icc.mpr hk) (fun hcontra => hne (by rw [hcontra]))

end ExteriorConvex
