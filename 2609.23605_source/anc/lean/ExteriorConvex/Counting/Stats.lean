/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung A of the article-2 formalisation: the two statistics and the matrix `A`

Formalisation of `def-stats` and `def-A` from
`article/exterior-convex_article2_draft_3.org`, per
`working-notes/PLAN-formalise-article2.org` (rung A).

* `Fn n` is article 2's `𝓕_n`: the finite set of `f`-vectors of **order
  ideals** of `𝒫([n])` — convention (i), void family included, so the
  membership condition is `IsOrderIdeal` with no further hypothesis.  The
  vectors are ℕ-valued (`fvecN`), living in `Fin (n+1) → ℕ`; the bridge to
  the ℝ-valued `fvec`/`Sset` of `Spine/Complexes.lean` is
  `Sset_eq_image_SnF` in `Counting/Duality.lean`.
* `top` is `def-stats`' `tp(s⃗) = max{j : s(j) > 0}`, ℤ-valued so that the
  boundary convention `tp = −1` for the void family is the honest value, not
  an encoding.  `indeg(s⃗) = min{j : s(j) < C(n,j)}` stays ℕ-valued with the
  boundary convention `indeg = n+1` for the full simplex.  These conventions
  are load-bearing: they are what makes Alexander duality
  (`Counting/Duality.lean`) an involution of all of `𝓕_n`.
* `Amat n τ ρ` is `def-A`'s joint-distribution matrix, defined **by
  counting** and for *all* integer indices (it vanishes off the printed
  range `τ ∈ {−1,…,n}`, `ρ ∈ {0,…,n+1}`), which lets `cor-persymmetry` be
  stated without index-range side conditions.  Per the plan, Linusson's
  `E^p(n,k)` is never mentioned: `lem-joint` is a computational shortcut,
  not the definition of record.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`); the entries of `A` at small `n` are finite counts that
would tempt a decision procedure, and stay Sage verifications, deliberately.
-/
import ExteriorConvex.Spine.Complexes

open Finset

namespace ExteriorConvex

variable {n : ℕ}

/-! ## `𝓕_n` as a finite set of ℕ-valued `f`-vectors -/

/-- The ℕ-valued `f`-vector of a family, as a point of `Fin (n+1) → ℕ`.
Same entries as `Complexes.lean`'s `fvec`, before the single cast to ℝ. -/
def fvecN (D : Finset (Finset (Fin n))) : Fin (n + 1) → ℕ :=
  fun j => fEntry D j.val

@[simp] theorem fvecN_apply (D : Finset (Finset (Fin n))) (j : Fin (n + 1)) :
    fvecN D j = fEntry D j.val := rfl

instance : DecidablePred (IsOrderIdeal (n := n)) := fun D =>
  decidable_of_iff (∀ s ∈ D, ∀ t ∈ s.powerset, t ∈ D) (by
    constructor
    · intro h s t hs hts
      exact h s hs t (mem_powerset.mpr hts)
    · intro h s hs t ht
      exact h hs (mem_powerset.mp ht))

/-- `def-fn`: `𝓕_n`, the set of `f`-vectors of order ideals of `𝒫([n])` —
convention (i), so the void family's `0⃗` and the full simplex's vector are
both members. -/
def Fn (n : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (univ.filter fun D : Finset (Finset (Fin n)) => IsOrderIdeal D).image fvecN

theorem mem_Fn {s : Fin (n + 1) → ℕ} :
    s ∈ Fn n ↔ ∃ D, IsOrderIdeal D ∧ fvecN D = s := by
  simp [Fn]

/-- Entrywise bound on `𝓕_n`: `s(j) ≤ C(n,j)`. -/
theorem apply_le_choose_of_mem_Fn {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n)
    (j : Fin (n + 1)) : s j ≤ n.choose j.val := by
  obtain ⟨D, -, rfl⟩ := mem_Fn.mp hs
  exact fEntry_le_choose D j.val

/-- The void family's `f`-vector `0⃗` belongs to `𝓕_n` — convention (i). -/
theorem zero_mem_Fn : (0 : Fin (n + 1) → ℕ) ∈ Fn n :=
  mem_Fn.mpr ⟨∅, fun s _ hs _ => absurd hs (notMem_empty s),
    by funext j; simp⟩

/-- The `f`-vector of the full simplex `𝒫([n])`: `j ↦ C(n,j)`. -/
def fullVec (n : ℕ) : Fin (n + 1) → ℕ := fun j => n.choose j.val

/-- The full simplex realises the binomial bound in every degree. -/
theorem fEntry_univ (j : ℕ) :
    fEntry (univ : Finset (Finset (Fin n))) j = n.choose j := by
  rw [fEntry]
  have h : (univ : Finset (Finset (Fin n))).filter (fun s => #s = j) =
      Finset.univ.powersetCard j := by
    ext s
    simp [Finset.mem_powersetCard, subset_univ]
  rw [h, card_powersetCard, card_univ, Fintype.card_fin]

/-- The full simplex's `f`-vector belongs to `𝓕_n`. -/
theorem fullVec_mem_Fn : fullVec n ∈ Fn n :=
  mem_Fn.mpr ⟨univ, fun _ t _ _ => mem_univ t,
    by funext j; simp [fvecN, fEntry_univ, fullVec]⟩

/-! ## `def-stats`: the two statistics

`top` is ℤ-valued (the void family has `top = −1`); `indeg` is ℕ-valued
(the full simplex has `indeg = n+1`). -/

/-- `def-stats`: `tp(s⃗) = max{j : s(j) > 0}`, with `tp = −1` for the void
family. -/
def top (s : Fin (n + 1) → ℕ) : ℤ :=
  if h : (univ.filter fun j : Fin (n + 1) => 0 < s j).Nonempty
  then (((univ.filter fun j : Fin (n + 1) => 0 < s j).max' h).val : ℤ)
  else -1

/-- `def-stats`: `indeg(s⃗) = min{j : s(j) < C(n,j)}`, with `indeg = n+1`
for the full simplex. -/
def indeg (s : Fin (n + 1) → ℕ) : ℕ :=
  if h : (univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).Nonempty
  then ((univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).min' h).val
  else n + 1

/-! ### Range bounds -/

theorem neg_one_le_top (s : Fin (n + 1) → ℕ) : -1 ≤ top s := by
  rw [top]; split_ifs <;> omega

theorem top_le (s : Fin (n + 1) → ℕ) : top s ≤ (n : ℤ) := by
  rw [top]; split_ifs with h
  · have := Fin.is_le ((univ.filter fun j : Fin (n + 1) => 0 < s j).max' h)
    omega
  · omega

theorem indeg_le (s : Fin (n + 1) → ℕ) : indeg s ≤ n + 1 := by
  rw [indeg]; split_ifs with h
  · have := Fin.is_le
      ((univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).min' h)
    omega
  · omega

/-! ### Characterisations -/

theorem le_top_of_pos {s : Fin (n + 1) → ℕ} {j : Fin (n + 1)}
    (h : 0 < s j) : (j.val : ℤ) ≤ top s := by
  have hj : j ∈ univ.filter fun i : Fin (n + 1) => 0 < s i :=
    mem_filter.mpr ⟨mem_univ j, h⟩
  rw [top]
  split_ifs with hne
  · exact_mod_cast (Fin.le_def.mp (le_max' _ j hj))
  · exact absurd ⟨j, hj⟩ hne

theorem apply_eq_zero_of_top_lt {s : Fin (n + 1) → ℕ} {j : Fin (n + 1)}
    (h : top s < j.val) : s j = 0 := by
  by_contra hne
  exact absurd (le_top_of_pos (Nat.pos_of_ne_zero hne)) (not_le.mpr h)

@[simp] theorem top_zero : top (0 : Fin (n + 1) → ℕ) = -1 := by
  rw [top]
  split_ifs with hne
  · simp at hne
  · rfl

/-- `tp = −1` characterises the void family. -/
theorem top_eq_neg_one_iff {s : Fin (n + 1) → ℕ} : top s = -1 ↔ s = 0 := by
  constructor
  · intro h
    funext j
    exact apply_eq_zero_of_top_lt (by omega : top s < (j.val : ℤ))
  · rintro rfl
    exact top_zero

theorem indeg_le_of_lt {s : Fin (n + 1) → ℕ} {j : Fin (n + 1)}
    (h : s j < n.choose j.val) : indeg s ≤ j.val := by
  have hj : j ∈ univ.filter fun i : Fin (n + 1) => s i < n.choose i.val :=
    mem_filter.mpr ⟨mem_univ j, h⟩
  rw [indeg]
  split_ifs with hne
  · exact Fin.le_def.mp (min'_le _ j hj)
  · exact absurd ⟨j, hj⟩ hne

theorem choose_le_of_lt_indeg {s : Fin (n + 1) → ℕ} {j : Fin (n + 1)}
    (h : j.val < indeg s) : n.choose j.val ≤ s j := by
  by_contra hne
  exact absurd (indeg_le_of_lt (not_le.mp hne)) (not_le.mpr h)

/-- `indeg = n+1` characterises meeting the binomial bound everywhere. -/
theorem indeg_eq_succ_iff {s : Fin (n + 1) → ℕ} :
    indeg s = n + 1 ↔ ∀ j : Fin (n + 1), n.choose j.val ≤ s j := by
  constructor
  · intro h j
    exact choose_le_of_lt_indeg (by rw [h]; exact j.is_lt)
  · intro h
    rw [indeg]
    split_ifs with hne
    · exfalso
      obtain ⟨j, hj⟩ := hne
      exact absurd (mem_filter.mp hj).2 (not_lt.mpr (h j))
    · rfl

/-- The lower characterisation of `indeg`: `m ≤ indeg(s⃗)` iff the binomial
bound is met strictly below `m`. -/
theorem le_indeg_iff {s : Fin (n + 1) → ℕ} {m : ℕ} (hm : m ≤ n + 1) :
    m ≤ indeg s ↔ ∀ j : Fin (n + 1), j.val < m → n.choose j.val ≤ s j := by
  constructor
  · intro h j hj
    exact choose_le_of_lt_indeg (lt_of_lt_of_le hj h)
  · intro h
    rw [indeg]
    split_ifs with hne
    · by_contra hlt
      rw [not_le] at hlt
      have hmem := min'_mem _ hne
      have hval := (mem_filter.mp hmem).2
      exact absurd hval (not_lt.mpr (h _ hlt))
    · exact hm

@[simp] theorem indeg_zero : indeg (0 : Fin (n + 1) → ℕ) = 0 :=
  Nat.le_zero.mp (by
    have h0 : (0 : Fin (n + 1) → ℕ) 0 < n.choose (0 : Fin (n + 1)).val := by
      simp
    simpa using indeg_le_of_lt h0)

@[simp] theorem top_fullVec : top (fullVec n) = n := by
  have hmem : (⟨n, by omega⟩ : Fin (n + 1)) ∈
      univ.filter fun j : Fin (n + 1) => 0 < fullVec n j := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simp [fullVec]
  rw [top]
  split_ifs with hne
  · have h1 := Fin.is_le
      ((univ.filter fun j : Fin (n + 1) => 0 < fullVec n j).max' hne)
    have h2 : n ≤ ((univ.filter fun j : Fin (n + 1) =>
        0 < fullVec n j).max' hne).val :=
      Fin.le_def.mp (le_max' _ _ hmem)
    omega
  · exact absurd ⟨_, hmem⟩ hne

@[simp] theorem indeg_fullVec : indeg (fullVec n) = n + 1 :=
  indeg_eq_succ_iff.mpr fun _ => le_refl _

/-! ## The support condition `ρ ≤ τ + 1` -/

theorem indeg_le_of_top_lt {s : Fin (n + 1) → ℕ} {m : ℕ} (hm : m ≤ n)
    (h : top s < (m : ℤ)) : indeg s ≤ m := by
  have h0 : s ⟨m, by omega⟩ = 0 :=
    apply_eq_zero_of_top_lt (j := ⟨m, by omega⟩) h
  have hlt : indeg s ≤ (⟨m, by omega⟩ : Fin (n + 1)).val :=
    indeg_le_of_lt (by rw [h0]; exact Nat.choose_pos hm)
  exact hlt

/-- The support condition of `def-A`: `indeg(s⃗) ≤ tp(s⃗) + 1` always. -/
theorem indeg_le_top_add_one (s : Fin (n + 1) → ℕ) :
    (indeg s : ℤ) ≤ top s + 1 := by
  have h1 := neg_one_le_top s
  have h2 := top_le s
  by_cases h : top s + 1 ≤ (n : ℤ)
  · have hle : indeg s ≤ (top s + 1).toNat :=
      indeg_le_of_top_lt (by omega) (by omega)
    omega
  · have := indeg_le s
    omega

/-! ## `def-A`: the joint-distribution matrix -/

/-- `def-A`: `A[τ][ρ] = #{s⃗ ∈ 𝓕_n : tp(s⃗) = τ, indeg(s⃗) = ρ}`, defined
for all integer indices; it vanishes outside `τ ∈ {−1,…,n}`,
`ρ ∈ {0,…,n+1}`.  Defined by counting, per the plan — Linusson's
`E^p(n,k)` is not mentioned. -/
def Amat (n : ℕ) (τ ρ : ℤ) : ℕ :=
  ((Fn n).filter fun s => top s = τ ∧ (indeg s : ℤ) = ρ).card

/-- `def-A`'s support condition: `A` vanishes above the superdiagonal
`ρ = τ + 1`. -/
theorem Amat_eq_zero_of_add_one_lt {τ ρ : ℤ} (h : τ + 1 < ρ) :
    Amat n τ ρ = 0 := by
  rw [Amat, card_eq_zero, filter_eq_empty_iff]
  rintro s - ⟨htop, hindeg⟩
  have := indeg_le_top_add_one s
  omega

/-- `def-A`'s first corner entry: `A[−1][0] = 1`, the void family alone. -/
theorem Amat_corner_void (n : ℕ) : Amat n (-1) 0 = 1 := by
  rw [Amat]
  have h : (Fn n).filter (fun s => top s = -1 ∧ (indeg s : ℤ) = 0) =
      {(0 : Fin (n + 1) → ℕ)} := by
    ext s
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨-, htop, -⟩
      exact top_eq_neg_one_iff.mp htop
    · rintro rfl
      exact ⟨zero_mem_Fn, top_zero, by simp⟩
  rw [h, card_singleton]

/-- On `𝓕_n`, `indeg = n+1` pins the full simplex. -/
theorem eq_fullVec_of_indeg_eq_succ {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n)
    (h : indeg s = n + 1) : s = fullVec n := by
  funext j
  exact le_antisymm (apply_le_choose_of_mem_Fn hs j)
    (indeg_eq_succ_iff.mp h j)

/-- `def-A`'s second corner entry: `A[n][n+1] = 1`, the full simplex
alone. -/
theorem Amat_corner_full (n : ℕ) : Amat n n ((n : ℤ) + 1) = 1 := by
  rw [Amat]
  have h : (Fn n).filter
      (fun s => top s = (n : ℤ) ∧ (indeg s : ℤ) = (n : ℤ) + 1) =
      {fullVec n} := by
    ext s
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hsF, -, hindeg⟩
      exact eq_fullVec_of_indeg_eq_succ hsF (by omega)
    · rintro rfl
      refine ⟨fullVec_mem_Fn, top_fullVec, ?_⟩
      rw [indeg_fullVec]
      push_cast
      ring
  rw [h, card_singleton]

end ExteriorConvex
