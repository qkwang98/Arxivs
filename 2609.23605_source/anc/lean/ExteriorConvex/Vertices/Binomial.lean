/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 3: `lem-binomial-ratio`

Formalisation of §8.3's `lem-binomial-ratio` from `article/exterior-convex_article1_latest.org`.

The manuscript's ρ is `ρ j = C(n, d+j) / C(n, j)`, the ratio by which the two summands weight the
same shared coordinate.  The lemma says ρ is *strictly* decreasing -- but only on `1 ≤ j ≤ m`, where
`m = n - d`.  Beyond that both numerator and successor numerator vanish and the decrease is not
strict.  That range restriction was missing from an earlier draft of the manuscript and was put in
precisely because formalising the lemma forces the question; see
`working-notes/formalization-bridge-lemma.org`.
-/
import Mathlib

namespace ExteriorConvex

/-- The arithmetic core, with the manuscript's own computation: the two sides differ by
`d * (n + 1)`. -/
lemma key_ineq {n d j : ℕ} (hd : 1 ≤ d) (hdj : d + j ≤ n) :
    (n - d - j) * (j + 1) < (n - j) * (d + j + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = d + j + q := ⟨n - d - j, by omega⟩
  have h1 : d + j + q - d - j = q := by omega
  have h2 : d + j + q - j = d + q := by omega
  rw [h1, h2]
  nlinarith

/-- `lem-binomial-ratio` (1): positivity holds exactly up to `m = n - d`. -/
lemma choose_ratio_pos_iff {n d j : ℕ} (_hd : 1 ≤ d) (hj : 1 ≤ j) (hjn : j ≤ n) :
    0 < (n.choose (d + j) : ℝ) / (n.choose j : ℝ) ↔ j ≤ n - d := by
  have hB : 0 < (n.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hjn
  rw [div_pos_iff]
  constructor
  · rintro (⟨hnum, -⟩ | ⟨-, hden⟩)
    · by_contra hc
      have : n.choose (d + j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [this] at hnum; norm_num at hnum
    · linarith
  · intro hjm
    left
    refine ⟨?_, hB⟩
    exact_mod_cast Nat.choose_pos (show d + j ≤ n by omega)

/-- `lem-binomial-ratio` (2): the ratio is strictly decreasing on `1 ≤ j ≤ m`. -/
theorem choose_ratio_lt {n d j : ℕ} (hd : 1 ≤ d) (_hj : 1 ≤ j) (hdj : d + j ≤ n) :
    (n.choose (d + j + 1) : ℝ) / (n.choose (j + 1) : ℝ)
      < (n.choose (d + j) : ℝ) / (n.choose j : ℝ) := by
  have hjn : j ≤ n := by omega
  have hj1n : j + 1 ≤ n := by omega
  have hAn : 0 < n.choose (d + j) := Nat.choose_pos hdj
  have hBn : 0 < n.choose j := Nat.choose_pos hjn
  have hB1n : 0 < n.choose (j + 1) := Nat.choose_pos hj1n
  have hB : (0 : ℝ) < (n.choose j : ℝ) := by exact_mod_cast hBn
  have hB1 : (0 : ℝ) < (n.choose (j + 1) : ℝ) := by exact_mod_cast hB1n
  rw [div_lt_div_iff₀ hB1 hB]
  -- Reduce to a statement about natural numbers.
  have hnat : n.choose (d + j + 1) * n.choose j < n.choose (d + j) * n.choose (j + 1) := by
    have e1 : n.choose (d + j + 1) * (d + j + 1) = n.choose (d + j) * (n - (d + j)) :=
      Nat.choose_succ_right_eq n (d + j)
    have e2 : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) := Nat.choose_succ_right_eq n j
    have hsub : n - (d + j) = n - d - j := by omega
    have this : n.choose (d + j + 1) * n.choose j * ((d + j + 1) * (j + 1))
        < n.choose (d + j) * n.choose (j + 1) * ((d + j + 1) * (j + 1)) :=
      calc n.choose (d + j + 1) * n.choose j * ((d + j + 1) * (j + 1))
        = (n.choose (d + j + 1) * (d + j + 1)) * (n.choose j * (j + 1)) := by ring
      _ = (n.choose (d + j) * (n - d - j)) * (n.choose j * (j + 1)) := by rw [e1, hsub]
      _ = (n.choose (d + j) * n.choose j) * ((n - d - j) * (j + 1)) := by ring
      _ < (n.choose (d + j) * n.choose j) * ((n - j) * (d + j + 1)) := by
            exact mul_lt_mul_of_pos_left (key_ineq hd hdj) (Nat.mul_pos hAn hBn)
      _ = n.choose (d + j) * (n.choose j * (n - j)) * (d + j + 1) := by ring
      _ = n.choose (d + j) * (n.choose (j + 1) * (j + 1)) * (d + j + 1) := by rw [e2]
      _ = n.choose (d + j) * n.choose (j + 1) * ((d + j + 1) * (j + 1)) := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  exact_mod_cast hnat

/-- The tail of `lem-binomial-ratio`: beyond `m` the ratio is identically zero, so the decrease
there is *not* strict.  This is the content of the range restriction. -/
lemma choose_ratio_eq_zero {n d j : ℕ} (_hj : 1 ≤ j) (_hjn : j ≤ n) (hjm : n - d < j)
    (_hd : 1 ≤ d) :
    (n.choose (d + j) : ℝ) / (n.choose j : ℝ) = 0 := by
  have : n.choose (d + j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [this]
  simp

end ExteriorConvex
