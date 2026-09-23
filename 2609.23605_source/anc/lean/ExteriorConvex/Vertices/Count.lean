/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# `cor-vdesc`: the vertex count

Formalisation of §8.4's `cor-vdesc` from `article/exterior-convex_article1_latest.org`:
the rank-two Kozlov polytope has exactly `n² − (m−1)(m+2)/2` vertices, where `m = n − d`.

This is the one part of §8 that is a *cardinality computation* rather than a construction, and it
needs two inputs that nothing before it needed:

* `eq_of_add_eq_of_mem_extremePoints` (in `Bridge.lean`) — a vertex of a Minkowski sum decomposes in
  exactly one way, which is what makes `(i,j) ↦ v_i + u_j` injective on the surviving pairs;
* `extremal_matrix_iff` (in `Kozlov.lean`) — the classification itself, which identifies the vertex
  set with the image of an explicit `Finset` of index pairs.

The count is then arithmetic: the zero set has `t − 1` entries below the diagonal in the row with
`t = i − d`, plus one more at `j = t + 1` when that stays inside the block, and
`∑_{t=1}^{m} (t−1) + (m−1) = (m−1)(m+2)/2`.  It is stated below in the subtraction-free form
`2 * card = (m−1)*(m+2)` as well, since that is what the proof actually establishes.
-/
import Mathlib
import ExteriorConvex.Vertices.Bridge
import ExteriorConvex.Vertices.ExtremalMatrix

namespace ExteriorConvex

open Finset Pointwise

variable {N : ℕ}

/-- The condition under which the extremal matrix entry vanishes, as in `extremal_matrix_iff`. -/
def zeroCond (n d : ℕ) (p : ℕ × ℕ) : Prop :=
  d + 1 ≤ p.1 ∧ p.2 ≤ n - d ∧ (p.2 + d < p.1 ∨ p.1 + 1 = d + p.2)

instance (n d : ℕ) (p : ℕ × ℕ) : Decidable (zeroCond n d p) := by
  unfold zeroCond; infer_instance

/-- The index pairs that give vertices. -/
def survivingPairs (n d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => ¬ zeroCond n d p)

/-- The index pairs that do not. -/
def zeroPairs (n d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (zeroCond n d)

lemma card_all (n : ℕ) : (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).card = n ^ 2 := by
  rw [Finset.card_product, Nat.card_Icc]
  simp [sq]

lemma card_surviving_add_card_zero (n d : ℕ) :
    (survivingPairs n d).card + (zeroPairs n d).card = n ^ 2 := by
  classical
  rw [← card_all n, survivingPairs, zeroPairs, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : zeroCond n d p <;> simp [h]

/-! ### The arithmetic of the zero set -/

/-- The row count: in the row with `t = i - d`, the zero set has `t - 1` entries strictly below the
diagonal, plus one at `j = t + 1` when that index is still inside the block. -/
lemma card_row (n m t : ℕ) (hmn : m ≤ n) (ht1 : 1 ≤ t) (htm : t ≤ m) :
    ((Finset.Icc 1 n).filter (fun j => j ≤ m ∧ (j < t ∨ j = t + 1))).card
      = (t - 1) + (if t + 1 ≤ m then 1 else 0) := by
  by_cases h : t + 1 ≤ m
  · have hset : (Finset.Icc 1 n).filter (fun j => j ≤ m ∧ (j < t ∨ j = t + 1))
        = insert (t + 1) (Finset.Icc 1 (t - 1)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (t + 1) ∉ Finset.Icc 1 (t - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hset, Finset.card_insert_of_notMem hnot, Nat.card_Icc, if_pos h]
    omega
  · have hset : (Finset.Icc 1 n).filter (fun j => j ≤ m ∧ (j < t ∨ j = t + 1))
        = Finset.Icc 1 (t - 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hset, Nat.card_Icc, if_neg h]
    omega

/-- The zero set has `(m−1)(m+2)/2` members, stated without division. -/
theorem card_zeroPairs (n d : ℕ) (hd : 1 ≤ d) (hdn : d + 1 ≤ n) :
    2 * (zeroPairs n d).card = (n - d - 1) * (n - d + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = d + m := ⟨n - d, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmn : m ≤ d + m := by omega
  have hsub0 : d + m - d = m := by omega
  rw [hsub0]
  -- Count row by row.
  have hrow : (zeroPairs (d + m) d).card
      = ∑ i ∈ Finset.Icc 1 (d + m),
          ((Finset.Icc 1 (d + m)).filter (fun j => zeroCond (d + m) d (i, j))).card := by
    rw [zeroPairs, Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun i _ => (Finset.card_filter _ _).symm)
  -- Rows below `d + 1` contribute nothing; the others contribute `card_row`.
  have hval : ∀ i ∈ Finset.Icc 1 (d + m),
      ((Finset.Icc 1 (d + m)).filter (fun j => zeroCond (d + m) d (i, j))).card
        = if d + 1 ≤ i then (i - d - 1) + (if i - d + 1 ≤ m then 1 else 0) else 0 := by
    intro i hi
    simp only [Finset.mem_Icc] at hi
    by_cases h : d + 1 ≤ i
    · rw [if_pos h]
      have hcongr : ((Finset.Icc 1 (d + m)).filter (fun j => zeroCond (d + m) d (i, j)))
          = ((Finset.Icc 1 (d + m)).filter (fun j => j ≤ m ∧ (j < i - d ∨ j = (i - d) + 1))) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, zeroCond, hsub0]
        omega
      rw [hcongr, card_row (d + m) m (i - d) hmn (by omega) (by omega)]
    · rw [if_neg h]
      have hempty : ((Finset.Icc 1 (d + m)).filter (fun j => zeroCond (d + m) d (i, j))) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, zeroCond, hsub0, Finset.notMem_empty,
          iff_false]
        omega
      rw [hempty, Finset.card_empty]
  rw [hrow, Finset.sum_congr rfl hval]
  -- Drop the rows below `d + 1`, then reindex `i = d + 1 + k`.
  have hsum : ∑ i ∈ Finset.Icc 1 (d + m),
      (if d + 1 ≤ i then (i - d - 1) + (if i - d + 1 ≤ m then 1 else 0) else 0)
      = ∑ k ∈ Finset.range m, (k + (if k + 2 ≤ m then 1 else 0)) := by
    have hsub : Finset.Icc (d + 1) (d + m) ⊆ Finset.Icc 1 (d + m) := by
      intro x hx; simp only [Finset.mem_Icc] at *; omega
    rw [← Finset.sum_subset hsub (by
      intro x hx hnx
      simp only [Finset.mem_Icc] at hx hnx
      rw [if_neg (by omega)])]
    rw [show Finset.Icc (d + 1) (d + m) = Finset.Ico (d + 1) (d + m + 1) from
        (Finset.Ico_add_one_right_eq_Icc _ _).symm,
      Finset.sum_Ico_eq_sum_range]
    have hlen : d + m + 1 - (d + 1) = m := by omega
    rw [hlen]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    have e1 : d + 1 + k - d - 1 = k := by omega
    have e2 : d + 1 + k - d + 1 = k + 2 := by omega
    rw [if_pos (by omega), e1, e2]
  rw [hsum, Finset.sum_add_distrib]
  have h1 : (∑ k ∈ Finset.range m, k) * 2 = m * (m - 1) := Finset.sum_range_id_mul_two m
  have h2 : (∑ k ∈ Finset.range m, (if k + 2 ≤ m then 1 else 0)) = m - 1 := by
    rw [← Finset.card_filter]
    have hf : (Finset.range m).filter (fun k => k + 2 ≤ m) = Finset.range (m - 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf, Finset.card_range]
  have hkey : (m - 1) * (m + 2) = m * (m - 1) + 2 * (m - 1) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [h2, hkey, ← h1]
  ring

/-! ### The geometry: the vertex set is the image of the surviving pairs -/

/-- The vertex set of the rank-two sum, as the image of an explicit `Finset` of index pairs. -/
theorem vertices_eq_image {n d : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hdec : ∀ s, 1 ≤ s → s < n - d → rho a d (s + 1) < rho a d s) :
    Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n))
      = ↑((survivingPairs n d).image (fun p => ravA a N 0 p.1 + ravA a N d p.2)) := by
  ext x
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · intro hx
    have hx' := hx
    rw [← convexHull_add] at hx'
    obtain ⟨s, hs, t, ht, rfl⟩ := extremePoints_convexHull_subset hx'
    obtain ⟨i, hi, rfl⟩ := hs
    obtain ⟨j, hj, rfl⟩ := ht
    simp only [Set.mem_Icc] at hi hj
    refine ⟨(i, j), ?_, rfl⟩
    rw [survivingPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hi, hj⟩, (extremal_matrix_iff a hpos hN hd hdn hdec hi.1 hi.2 hj.1 hj.2).mp hx⟩
  · rintro ⟨p, hp, rfl⟩
    rw [survivingPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨hi, hj⟩, hcond⟩ := hp
    exact (extremal_matrix_iff a hpos hN hd hdn hdec hi.1 hi.2 hj.1 hj.2).mpr hcond

/-- Distinct surviving pairs give distinct vertices: a vertex has only one decomposition. -/
theorem image_injOn {n d : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hdec : ∀ s, 1 ≤ s → s < n - d → rho a d (s + 1) < rho a d s) :
    Set.InjOn (fun p : ℕ × ℕ => ravA a N 0 p.1 + ravA a N d p.2) (survivingPairs n d) := by
  intro p hp q hq hEq
  simp only [Finset.mem_coe, survivingPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc] at hp hq
  obtain ⟨⟨hp1, hp2⟩, hpc⟩ := hp
  obtain ⟨⟨hq1, hq2⟩, hqc⟩ := hq
  -- The common value is a vertex, so its decomposition is unique.
  have hvert : ravA a N 0 p.1 + ravA a N d p.2 ∈
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) :=
    (extremal_matrix_iff a hpos hN hd hdn hdec hp1.1 hp1.2 hp2.1 hp2.2).mpr hpc
  have hmem : ∀ (dd k : ℕ), 1 ≤ k → k ≤ n →
      ravA a N dd k ∈ convexHull ℝ (vsetA a N dd n) :=
    fun dd k h1 h2 => subset_convexHull ℝ _ (ravA_mem_vsetA h1 h2)
  obtain ⟨e1, e2⟩ := eq_of_add_eq_of_mem_extremePoints hvert
    (hmem 0 p.1 hp1.1 hp1.2) (hmem d p.2 hp2.1 hp2.2)
    (hmem 0 q.1 hq1.1 hq1.2) (hmem d q.2 hq2.1 hq2.2) rfl hEq.symm
  have h1 : p.1 = q.1 :=
    ravA_injOn a hpos (n := n) (by omega) ⟨hp1.1, hp1.2⟩ ⟨hq1.1, hq1.2⟩ e1
  have h2 : p.2 = q.2 :=
    ravA_injOn a hpos (n := n) (by omega) ⟨hp2.1, hp2.2⟩ ⟨hq2.1, hq2.2⟩ e2
  exact Prod.ext h1 h2

/-- **`cor-vdesc`.**  The rank-two sum has exactly `n² − (m−1)(m+2)/2` vertices, `m = n − d`. -/
theorem card_vertices {n d : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hdec : ∀ s, 1 ≤ s → s < n - d → rho a d (s + 1) < rho a d s) :
    (Set.extremePoints ℝ
        (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n))).ncard
      = n ^ 2 - (n - d - 1) * (n - d + 2) / 2 := by
  rw [vertices_eq_image a hpos hN hd hdn hdec, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (image_injOn a hpos hN hd hdn hdec)]
  have h1 := card_surviving_add_card_zero n d
  have h2 := card_zeroPairs n d hd hdn
  omega

/-- **`cor-vdesc` for the Kozlov vector**, which is how the manuscript states it: the rank-two
Kozlov polytope has `n² − (m−1)(m+2)/2` vertices. -/
theorem card_vertices_kozlov {n d : ℕ} (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n) :
    (Set.extremePoints ℝ
        (convexHull ℝ (vsetA (kozLeg n) N 0 n)
          + convexHull ℝ (vsetA (kozLeg n) N d n))).ncard
      = n ^ 2 - (n - d - 1) * (n - d + 2) / 2 := by
  refine card_vertices _ (kozLeg_pos n) hN hd hdn ?_
  intro s hs1 hs2
  have e : d + (s + 1) = d + s + 1 := by omega
  simp only [rho, kozLeg, e]
  rw [if_pos (show d + s + 1 ≤ n by omega), if_pos (show s + 1 ≤ n by omega),
    if_pos (show d + s ≤ n by omega), if_pos (show s ≤ n by omega)]
  exact choose_ratio_lt hd hs1 (by omega)

end ExteriorConvex
