/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 2 of the §§4–6 formalisation: local LYM and the chain description

Formalisation of `lem-lym` and `lem-mu` from
`article/exterior-convex_article1_latest.org`, per
`working-notes/PLAN-formalise-rungs-1-4.org`.

* `lym` is `lem-lym`, the local Lubell–Yamamoto–Meshalkin inequality for an
  order ideal, transported from Mathlib's downward-shadow form
  (`Finset.local_lubell_yamamoto_meshalkin_inequality_div`): Mathlib indexes
  downward through the shadow `∂𝒜`; our statement is upward on a
  downward-closed family, and downward closure gives `∂𝒜 ⊆ {σ ∈ Δ : |σ| = j}`.
* `skel n j` is `eq:skeleton` in the degree-0-inclusive space: the `f`-vector
  of the complete `j`-skeleton, with the leading `1` the manuscript's `F̃_j`
  drops (see the footnote to `eq:skeleton` — the tilde is Kozlov's, the
  dropped entry is ours, and here we keep it).
* `hull_skel_eq` is `lem-mu`, the LYM-chain description of
  `conv{F̃_1,…,F̃_n}`, inclusively.  The affine-independence / "this is an
  `(n-1)`-simplex" clause of `lem-mu` is **deliberately not formalised**
  (plan, Rung 2: not needed for rungs 3–4).
-/
import Mathlib
import ExteriorConvex.Spine.Complexes

open Finset
open scoped FinsetFamily

namespace ExteriorConvex

variable {n : ℕ}

/-! ## Local LYM, transported -/

/-- `lem-lym`: for an order ideal `Δ ∈ 𝒟_n` and `1 ≤ j ≤ n - 1`,
`f_{j+1}(Δ)/C(n,j+1) ≤ f_j(Δ)/C(n,j)`.

Transported from Mathlib's
`Finset.local_lubell_yamamoto_meshalkin_inequality_div`, which bounds `#𝒜`
against its shadow `#(∂𝒜)`: take `𝒜` to be the `(j+1)`-faces of `Δ`; downward
closure puts `∂𝒜` among the `j`-faces.

(The hypotheses `hj`, `hjn` are the manuscript's range; the Lean proof does
not need them, but the statement keeps them to match `lem-lym` exactly.) -/
theorem lym {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D) {j : ℕ}
    (_hj : 1 ≤ j) (_hjn : j ≤ n - 1) :
    (fEntry D (j + 1) : ℝ) / (n.choose (j + 1) : ℝ) ≤
      (fEntry D j : ℝ) / (n.choose j : ℝ) := by
  classical
  set 𝒜 : Finset (Finset (Fin n)) := D.filter (fun s => #s = j + 1) with h𝒜
  have hsized : (𝒜 : Set (Finset (Fin n))).Sized (j + 1) := fun s hs =>
    (mem_filter.mp hs).2
  have hlym := Finset.local_lubell_yamamoto_meshalkin_inequality_div
    (𝕜 := ℝ) j.succ_ne_zero hsized
  rw [Fintype.card_fin, Nat.succ_sub_one] at hlym
  have hshadow : ∂ 𝒜 ⊆ D.filter (fun s => #s = j) := by
    intro t ht
    rw [mem_shadow_iff] at ht
    obtain ⟨s, hs, a, ha, rfl⟩ := ht
    rw [mem_filter] at hs ⊢
    exact ⟨hD hs.1 (erase_subset a s),
      by rw [card_erase_of_mem ha, hs.2]; omega⟩
  have hle : (#(∂ 𝒜) : ℝ) ≤ (fEntry D j : ℝ) := by
    exact_mod_cast card_le_card hshadow
  calc (fEntry D (j + 1) : ℝ) / (n.choose (j + 1) : ℝ)
      = (#𝒜 : ℝ) / (n.choose (j + 1) : ℝ) := rfl
    _ ≤ (#(∂ 𝒜) : ℝ) / (n.choose j : ℝ) := hlym
    _ ≤ (fEntry D j : ℝ) / (n.choose j : ℝ) := by gcongr

/-! ## The skeleta and the LYM chain -/

/-- `eq:skeleton`, in the degree-0-inclusive space: the `f`-vector of the
complete `j`-skeleton on `[n]` — entry `0` is `1`, entries `1..j` are
`C(n,i)`, the rest `0`. -/
def skel (n j : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if i.val = 0 then 1 else if i.val ≤ j then (n.choose i.val : ℝ) else 0

/-- The set of skeleta `{F̃_1, …, F̃_n}`, inclusively. -/
def skelSet (n : ℕ) : Set (Fin (n + 1) → ℝ) := skel n '' Set.Icc 1 n

/-- The right-hand side of `eq:mu` (`lem-mu`), in inclusive coordinates:
`x₀ = 1`, `μ₁ = 1` (i.e. `x₁ = n`), the LYM chain `μ_j ≥ μ_{j+1}` for
`1 ≤ j ≤ n-1`, and `μ_n ≥ 0`. -/
def lymChain (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = 1 ∧ x 1 = (n : ℝ) ∧
    (∀ j, (hj : 1 ≤ j) → (hjn : j ≤ n - 1) →
      x ⟨j + 1, by omega⟩ / (n.choose (j + 1) : ℝ) ≤
        x ⟨j, by omega⟩ / (n.choose j : ℝ)) ∧
    0 ≤ x (Fin.last n)}

/-- For `n ≥ 1` the `Fin`-literal `1` really is the coordinate `1`.
(Utility; rung 3 uses it too.) -/
theorem fin_one_eq (hn : 1 ≤ n) :
    (1 : Fin (n + 1)) = ⟨1, by omega⟩ := by
  apply Fin.ext
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

/-- The chain set is convex: an intersection of two hyperplanes and finitely
many half-spaces, checked directly. -/
theorem convex_lymChain (n : ℕ) : Convex ℝ (lymChain n) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx0, hy0, mul_one]
    exact hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx1, hy1]
    rw [← add_mul, hab, one_mul]
  · intro j hj hjn
    have h1 := hxc j hj hjn
    have h2 := hyc j hj hjn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div,
      mul_div_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha)
      (mul_le_mul_of_nonneg_left h2 hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hxn) (mul_nonneg hb hyn)

/-- Each skeleton satisfies the chain description: `skelSet n ⊆` the RHS of
`eq:mu`.  (The easy half of the manuscript's `lem-mu` computation.) -/
theorem skelSet_subset_lymChain (hn : 1 ≤ n) : skelSet n ⊆ lymChain n := by
  rintro _ ⟨j, hj, rfl⟩
  rw [Set.mem_Icc] at hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [skel]
  · rw [fin_one_eq hn]
    simp only [skel]
    rw [ite_eq_right one_ne_zero, ite_eq_left hj.1, Nat.choose_one_right]
  · intro k hk hkn
    have hCk : ((n.choose k : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have hCk1 : ((n.choose (k + 1) : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    simp only [skel]
    rw [ite_eq_right (by omega : ¬(k + 1 = 0)), ite_eq_right (by omega : ¬(k = 0))]
    split_ifs with h1 h2 h2
    · rw [div_self hCk1, div_self hCk]
    · omega
    · rw [zero_div, div_self hCk]
      exact zero_le_one
    · rw [zero_div, zero_div]
  · simp only [skel, Fin.val_last]
    rw [ite_eq_right (by omega : ¬(n = 0))]
    split_ifs with h
    · exact Nat.cast_nonneg _
    · exact le_refl 0

/-! ## The reverse inclusion: reconstructing the convex combination

The manuscript's barycentric computation (`lem-mu`'s proof):
`λ_j = μ_j − μ_{j+1}` for `j < n`, `λ_n = μ_n`.  Here `muOf` is made total
with value `0` beyond `n`, so that uniformly `λ_j = μ_j − μ_{j+1}` on
`1 ≤ j ≤ n` and the sum telescopes.

(These four declarations were `private` until 2026-09-14; rung 5
(`Permissive.lean`, `lem-mu-permissive`) reuses the identical telescoping
machinery with the sum extended to start at `j = 0`, so they are now public.
Nothing about their statements or proofs changed.) -/

/-- The LYM ratio `μ_k(x) = x_k / C(n,k)` (`def-lym-ratios`), as a total
function of `k : ℕ`, zero beyond `n`. -/
noncomputable def muOf (n : ℕ) (x : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ n then x ⟨k, Nat.lt_succ_of_le h⟩ / (n.choose k : ℝ) else 0

theorem muOf_of_le {x : Fin (n + 1) → ℝ} {k : ℕ} (h : k ≤ n) :
    muOf n x k = x ⟨k, Nat.lt_succ_of_le h⟩ / (n.choose k : ℝ) :=
  dite_eq_left h

theorem muOf_of_gt {x : Fin (n + 1) → ℝ} {k : ℕ} (h : n < k) :
    muOf n x k = 0 :=
  dite_eq_right (by omega)

/-- Telescoping: `∑_{j=k}^{n} (μ_j − μ_{j+1}) = μ_k` for `k ≤ n`. -/
theorem sum_mu_telescope (x : Fin (n + 1) → ℝ) {k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.Icc k n, (muOf n x j - muOf n x (j + 1)) = muOf n x k := by
  have hIcc : Finset.Icc k n = Finset.Ico k (n + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hcongr : ∀ i ∈ Finset.range (n + 1 - k),
      muOf n x (k + i) - muOf n x (k + i + 1) =
        (fun i => muOf n x (k + i)) i - (fun i => muOf n x (k + i)) (i + 1) := by
    intro i _
    simp only []
    rw [← Nat.add_assoc]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub' (fun i => muOf n x (k + i))]
  simp only [Nat.add_zero]
  rw [show k + (n + 1 - k) = n + 1 by omega, muOf_of_gt (Nat.lt_succ_self n),
    sub_zero]

/-- The hard half of `lem-mu`: a point of the chain set is a convex
combination of the skeleta, with barycentric coordinates
`λ_j = μ_j − μ_{j+1}`, `λ_n = μ_n`. -/
theorem lymChain_subset_hull (hn : 1 ≤ n) :
    lymChain n ⊆ convexHull ℝ (skelSet n) := by
  intro x hx
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  set w : ℕ → ℝ := fun j => muOf n x j - muOf n x (j + 1) with hw
  -- μ₁ = 1, from x₁ = n.
  have hmu1 : muOf n x 1 = 1 := by
    rw [muOf_of_le hn, ← fin_one_eq hn, hx1, Nat.choose_one_right,
      div_self (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
  -- The weights are non-negative.
  have hw0 : ∀ j ∈ Finset.Icc 1 n, 0 ≤ w j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases eq_or_lt_of_le hj.2 with hjn | hjn
    · subst hjn
      rw [hw]
      simp only []
      rw [muOf_of_gt (Nat.lt_succ_self j), sub_zero, muOf_of_le (le_refl j),
        Nat.choose_self, Nat.cast_one, div_one]
      exact hxn
    · have h := hxc j hj.1 (by omega)
      rw [hw]
      simp only []
      rw [muOf_of_le (by omega : j ≤ n), muOf_of_le (by omega : j + 1 ≤ n),
        sub_nonneg]
      exact h
  -- The weights sum to 1.
  have hsum : ∑ j ∈ Finset.Icc 1 n, w j = 1 := by
    rw [hw]
    rw [sum_mu_telescope x hn, hmu1]
  -- Each skeleton is a generator.
  have hz : ∀ j ∈ Finset.Icc 1 n, skel n j ∈ skelSet n := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Set.mem_image_of_mem _ (Set.mem_Icc.mpr hj)
  -- The convex combination reconstructs `x`.
  have hrepr : ∑ j ∈ Finset.Icc 1 n, w j • skel n j = x := by
    funext i
    rw [Finset.sum_apply]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · have hval : ∀ j ∈ Finset.Icc 1 n, (w j • skel n j) i = w j := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul,
          show skel n j i = 1 by simp [skel, hi0], mul_one]
      rw [Finset.sum_congr rfl hval, hsum]
      have hi : i = 0 := Fin.ext hi0
      rw [hi, hx0]
    · have hkn : i.val ≤ n := by omega
      have hval : ∀ j ∈ Finset.Icc 1 n, (w j • skel n j) i =
          if i.val ≤ j then w j * (n.choose i.val : ℝ) else 0 := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul]
        by_cases hkj : i.val ≤ j
        · rw [ite_eq_left hkj, show skel n j i = (n.choose i.val : ℝ) by
            simp only [skel]; rw [ite_eq_right (by omega), ite_eq_left hkj]]
        · rw [ite_eq_right hkj, show skel n j i = 0 by
            simp only [skel]; rw [ite_eq_right (by omega), ite_eq_right hkj], mul_zero]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
      have hfilter : (Finset.Icc 1 n).filter (fun j => i.val ≤ j) =
          Finset.Icc i.val n := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilter, ← Finset.sum_mul, sum_mu_telescope x hkn,
        muOf_of_le hkn,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne')]
  have hcm := Finset.centerMass_mem_convexHull (Finset.Icc 1 n) hw0
    (by rw [hsum]; exact zero_lt_one) hz
  rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hrepr] at hcm

/-- `lem-mu` (the LYM chain): the convex hull of the skeleta is exactly the
chain set.  The affine-independence clause ("an `(n−1)`-dimensional simplex")
is not formalised — see the file header. -/
theorem hull_skel_eq (hn : 1 ≤ n) :
    convexHull ℝ (skelSet n) = lymChain n :=
  Set.Subset.antisymm
    (convexHull_min (skelSet_subset_lymChain hn) (convex_lymChain n))
    (lymChain_subset_hull hn)

end ExteriorConvex
