/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 2: the combinatorial core of `thm-ones`

Formalisation of the engine of §8.2's `thm-ones` from
`article/exterior-convex_article1_latest.org`.

For the all-ones leg vector the pairing telescopes,
`⟪φ, shift^{d_p}(v_k)⟫ = Φ(d_p + k) - Φ(d_p)` with `Φ` the partial-sum sequence of `φ`, and the
extremal condition becomes: *is there a real sequence `Φ` whose strict maximum over each of two
windows falls at a prescribed point?*  The manuscript answers this by acyclicity of a digraph; at
rank two only `m₁` and `m₂` have outgoing edges, so a cycle is a 2-cycle and the general acyclicity
machinery is not needed.  `exists_strictMax_two_iff` below is that statement, and it needs nothing
about the windows at all -- not that they are intervals, not that they have equal length.

`thm_ones_windows` then does the arithmetic unwinding into the manuscript's `1 ≤ t ≤ m`,
`1 ≤ j ≤ m`, `t ≠ j`.
-/
import Mathlib

namespace ExteriorConvex

open Finset

/-- **The rank-two feasibility criterion.**  Two prescribed maxima over two finite sets are
simultaneously realisable by one real sequence exactly when they do not form a 2-cycle: that is,
unless the two prescribed points are distinct and each lies in the other's window.

This is the rank-two case of "a system of strict inequalities is solvable iff its digraph is
acyclic"; here the digraph has out-edges only at `m₁` and `m₂`, so acyclicity reduces to the
displayed condition and no digraph is needed. -/
theorem exists_strictMax_two_iff {α : Type*} [DecidableEq α] (W₁ W₂ : Finset α) (m₁ m₂ : α) :
    (∃ Φ : α → ℝ, (∀ x ∈ W₁, x ≠ m₁ → Φ x < Φ m₁) ∧ (∀ x ∈ W₂, x ≠ m₂ → Φ x < Φ m₂))
      ↔ ¬(m₁ ≠ m₂ ∧ m₂ ∈ W₁ ∧ m₁ ∈ W₂) := by
  constructor
  · rintro ⟨Φ, h₁, h₂⟩ ⟨hne, hm₂, hm₁⟩
    exact absurd (h₁ m₂ hm₂ (Ne.symm hne)) (not_lt.mpr (h₂ m₁ hm₁ hne).le)
  · intro h
    by_cases hEq : m₁ = m₂
    · -- The two prescriptions coincide: an indicator of the common point works.
      subst hEq
      refine ⟨fun x => if x = m₁ then 1 else 0, fun x _ hx => ?_, fun x _ hx => ?_⟩ <;>
        simp [hx]
    · -- Distinct prescriptions.  At least one of them is outside the other's window.
      rw [not_and, not_and] at h
      have hEq' : m₂ ≠ m₁ := fun hc => hEq hc.symm
      by_cases hA : m₂ ∈ W₁
      · -- then `m₁ ∉ W₂`; give `m₁` the strictly larger value, `m₂` the middle one.
        have hB : m₁ ∉ W₂ := h hEq hA
        set Φ : α → ℝ := fun x => if x = m₁ then 2 else if x = m₂ then 1 else 0 with hΦ
        have hv₁ : Φ m₁ = 2 := by simp [hΦ]
        have hv₂ : Φ m₂ = 1 := by simp [hΦ, hEq']
        have hle : ∀ x, x ≠ m₁ → Φ x ≤ 1 := by
          intro x hx
          simp only [hΦ]
          split_ifs with h1 h2
          · exact absurd h1 hx
          · norm_num
          · norm_num
        have hz : ∀ x, x ≠ m₁ → x ≠ m₂ → Φ x = 0 := by
          intro x hx hx2; simp [hΦ, hx, hx2]
        refine ⟨Φ, fun x _ hx => ?_, fun x hxW hx => ?_⟩
        · rw [hv₁]; exact lt_of_le_of_lt (hle x hx) (by norm_num)
        · have hxm₁ : x ≠ m₁ := fun hcontra => hB (hcontra ▸ hxW)
          rw [hv₂, hz x hxm₁ hx]; norm_num
      · -- `m₂ ∉ W₁`; give `m₂` the strictly larger value instead.
        set Φ : α → ℝ := fun x => if x = m₂ then 2 else if x = m₁ then 1 else 0 with hΦ
        have hv₂ : Φ m₂ = 2 := by simp [hΦ]
        have hv₁ : Φ m₁ = 1 := by simp [hΦ, hEq]
        have hle : ∀ x, x ≠ m₂ → Φ x ≤ 1 := by
          intro x hx
          simp only [hΦ]
          split_ifs with h1 h2
          · exact absurd h1 hx
          · norm_num
          · norm_num
        have hz : ∀ x, x ≠ m₂ → x ≠ m₁ → Φ x = 0 := by
          intro x hx hx2; simp [hΦ, hx, hx2]
        refine ⟨Φ, fun x hxW hx => ?_, fun x _ hx => ?_⟩
        · have hxm₂ : x ≠ m₂ := fun hcontra => hA (hcontra ▸ hxW)
          rw [hv₁, hz x hxm₂ hx]; norm_num
        · rw [hv₂]; exact lt_of_le_of_lt (hle x hx) (by norm_num)

/-- **`thm-ones`, in window form.**  With the manuscript's windows `W₁ = [1,n]` and
`W₂ = [d+1,d+n]`, prescribed points `m₁ = i` and `m₂ = d+j`, and `t = i - d`, `m = n - d`:
the pair is *in*feasible exactly on the manuscript's zero set `1 ≤ t ≤ m`, `1 ≤ j ≤ m`, `t ≠ j`.

Note `t ≤ m` and `1 ≤ j` are automatic from the index ranges; they are carried in the statement
only so that the zero set is self-contained, exactly as in the manuscript. -/
theorem thm_ones_windows {n d i j : ℕ} (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (_hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (_hjn : j ≤ n) :
    (∃ Φ : ℕ → ℝ, (∀ x ∈ Finset.Icc 1 n, x ≠ i → Φ x < Φ i) ∧
        (∀ x ∈ Finset.Icc (d + 1) (d + n), x ≠ d + j → Φ x < Φ (d + j)))
      ↔ ¬(1 ≤ i - d ∧ i - d ≤ n - d ∧ 1 ≤ j ∧ j ≤ n - d ∧ i - d ≠ j) := by
  rw [exists_strictMax_two_iff]
  constructor
  · intro h hzero
    exact h ⟨by omega, by simp only [Finset.mem_Icc]; omega,
      by simp only [Finset.mem_Icc]; omega⟩
  · rintro h ⟨hne, hm₂, hm₁⟩
    simp only [Finset.mem_Icc] at hm₂ hm₁
    exact h (by omega)

end ExteriorConvex
