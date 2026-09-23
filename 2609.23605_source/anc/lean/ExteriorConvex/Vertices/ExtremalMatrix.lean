/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 3: the general leg vector, and §8.3

`Simplex.lean` handles the all-ones leg vector, where a vertex is the *indicator* of a coordinate
interval and so the whole section collapses onto one partial-sum sequence.  For a general positive
leg vector the two summands weight the same shared coordinate differently -- which is exactly the
source of the leg-vector dependence the section is about -- and that collapse is unavailable.

The device used here avoids forming any explicit sums.  A vertex grows by *one* basis vector at a
time,

    ravA a d (k+1) = ravA a d k + a (k+1) • single ⟨d+k⟩ 1,

so applying a functional turns every comparison between consecutive vertices into a statement about
a single coefficient `f (single ⟨d+k⟩ 1)`, with the positive factor `a (k+1)` in front.  Monotonicity
of the vertex values along a run of coordinates is then ordinary monotonicity-from-increments, and
`prop-adjacent`'s sign contradiction becomes a two-line argument -- because *both* summands grow
across the same coordinate `⟨d+t⟩`, with opposite requirements on its coefficient.

**Index convention**, as in `Simplex.lean`: coordinates are `Fin N`, and `c : Fin N` stands for the
manuscript's coordinate `c.val + 1`.  Vertex indices run `1,…,n`.
-/
import Mathlib
import ExteriorConvex.Vertices.Bridge
import ExteriorConvex.Vertices.Simplex
import ExteriorConvex.Vertices.Binomial

namespace ExteriorConvex

open Finset Pointwise

variable {N : ℕ}

/-- The `k`-th vertex of the right-angle simplex on leg vector `a`, shifted by `d`: it carries the
value `a s` at the manuscript's coordinate `d + s`, for `1 ≤ s ≤ k`. -/
def ravA (a : ℕ → ℝ) (N d k : ℕ) : Fin N → ℝ :=
  fun c => if d + 1 ≤ c.val + 1 ∧ c.val + 1 ≤ d + k then a (c.val + 1 - d) else 0

@[simp] lemma ravA_zero (a : ℕ → ℝ) (N d : ℕ) : ravA a N d 0 = 0 := by
  funext c
  simp only [ravA, Nat.add_zero, Pi.zero_apply]
  rw [if_neg (by omega)]

/-- Vertices grow by one basis vector at a time, scaled by the corresponding leg. -/
lemma ravA_succ (a : ℕ → ℝ) (N d k : ℕ) (h : d + k < N) :
    ravA a N d (k + 1) = ravA a N d k + a (k + 1) • Pi.single (⟨d + k, h⟩ : Fin N) 1 := by
  funext c
  simp only [ravA, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hc : c = (⟨d + k, h⟩ : Fin N)
  · subst hc
    simp only [Fin.val_mk]
    rw [if_pos (by omega), if_neg (by omega)]
    have hidx : d + k + 1 - d = k + 1 := by omega
    rw [hidx]
    norm_num
  · have hne : c.val ≠ d + k := fun hh => hc (Fin.ext hh)
    rw [if_neg hc, mul_zero, add_zero]
    by_cases h1 : d + 1 ≤ c.val + 1 ∧ c.val + 1 ≤ d + k
    · rw [if_pos (by omega), if_pos h1]
    · rw [if_neg (by omega), if_neg h1]

/-- Applying a functional to consecutive vertices differs by one coefficient. -/
lemma map_ravA_succ (f : (Fin N → ℝ) →L[ℝ] ℝ) (a : ℕ → ℝ) (d k : ℕ) (h : d + k < N) :
    f (ravA a N d (k + 1))
      = f (ravA a N d k) + a (k + 1) * f (Pi.single (⟨d + k, h⟩ : Fin N) 1) := by
  rw [ravA_succ a N d k h, map_add, map_smul, smul_eq_mul]

/-- **`prop-adjacent`, upper side.**  No single functional can expose `v_{d+t}` on the first summand
and `u_{t+1}` on the second: both summands cross the coordinate `⟨d+t⟩`, and they need its
coefficient to have opposite signs.

The hypothesis `t + 1 ≤ n - d` is what makes this true and is exactly the qualifier an earlier draft
of the manuscript omitted.  It enters as `hup : d + t + 1 ≤ n`, which is what lets `v_{d+t+1}` exist
as a vertex of the first summand; without it there is no competitor to compare against. -/
theorem prop_adjacent_upper {n d t : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (ht : 1 ≤ t) (hup : d + t + 1 ≤ n)
    (f : (Fin N → ℝ) →L[ℝ] ℝ)
    (h₁ : ∀ k, 1 ≤ k → k ≤ n → k ≠ d + t → f (ravA a N 0 k) < f (ravA a N 0 (d + t)))
    (h₂ : ∀ k, 1 ≤ k → k ≤ n → k ≠ t + 1 → f (ravA a N d k) < f (ravA a N d (t + 1))) :
    False := by
  have hb : d + t < N := by omega
  -- The second summand must gain across the coordinate `⟨d+t⟩`.
  have hgain : f (ravA a N d t) < f (ravA a N d (t + 1)) := h₂ t ht (by omega) (by omega)
  rw [map_ravA_succ f a d t hb] at hgain
  have hepos : 0 < f (Pi.single (⟨d + t, hb⟩ : Fin N) 1) := by
    by_contra hc
    push Not at hc
    nlinarith [hpos (t + 1)]
  -- The first summand must lose across the same coordinate.
  have hb' : 0 + (d + t) < N := by omega
  have hloss : f (ravA a N 0 (d + t + 1)) < f (ravA a N 0 (d + t)) :=
    h₁ (d + t + 1) (by omega) hup (by omega)
  rw [show d + t + 1 = (d + t) + 1 from rfl, map_ravA_succ f a 0 (d + t) hb'] at hloss
  have : (⟨0 + (d + t), hb'⟩ : Fin N) = ⟨d + t, hb⟩ := by ext; simp
  rw [this] at hloss
  nlinarith [hpos (d + t + 1)]

/-- **`prop-adjacent`, lower side.**  The mirror image: `v_{d+t}` and `u_{t-1}` cannot be exposed
together either, this time because both summands cross the coordinate `⟨d+t-1⟩`. -/
theorem prop_adjacent_lower {n d t : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (ht : 2 ≤ t) (hd : 1 ≤ d) (htn : d + t ≤ n)
    (f : (Fin N → ℝ) →L[ℝ] ℝ)
    (h₁ : ∀ k, 1 ≤ k → k ≤ n → k ≠ d + t → f (ravA a N 0 k) < f (ravA a N 0 (d + t)))
    (h₂ : ∀ k, 1 ≤ k → k ≤ n → k ≠ t - 1 → f (ravA a N d k) < f (ravA a N d (t - 1))) :
    False := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hb : d + t' < N := by omega
  simp only [Nat.add_sub_cancel] at h₂
  -- The second summand must *lose* across `⟨d+t'⟩`.
  have hloss : f (ravA a N d (t' + 1)) < f (ravA a N d t') := h₂ (t' + 1) (by omega) (by omega)
    (by omega)
  rw [map_ravA_succ f a d t' hb] at hloss
  have hneg : f (Pi.single (⟨d + t', hb⟩ : Fin N) 1) < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [hpos (t' + 1)]
  -- The first summand must *gain* across the same coordinate.
  have hb' : 0 + (d + t') < N := by omega
  have hgain : f (ravA a N 0 (d + t')) < f (ravA a N 0 (d + t' + 1)) := by
    have hlt := h₁ (d + t') (by omega) (by omega) (by omega)
    have heq : d + (t' + 1) = d + t' + 1 := by omega
    rwa [heq] at hlt
  rw [show d + t' + 1 = (d + t') + 1 from rfl, map_ravA_succ f a 0 (d + t') hb'] at hgain
  have : (⟨0 + (d + t'), hb'⟩ : Fin N) = ⟨d + t', hb⟩ := by ext; simp
  rw [this] at hgain
  nlinarith [hpos (d + t' + 1)]

/-- Consecutive vertices are distinct, because the leg they differ by is non-zero.  This is all the
injectivity the geometric statement below needs -- much less than the full `rav_injOn`. -/
lemma ravA_succ_ne (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) (N d k : ℕ) (h : d + k < N) :
    ravA a N d (k + 1) ≠ ravA a N d k := by
  intro hEq
  have hc := congrFun hEq (⟨d + k, h⟩ : Fin N)
  simp only [ravA, Fin.val_mk] at hc
  rw [if_pos (by omega), if_neg (by omega)] at hc
  have hidx : d + k + 1 - d = k + 1 := by omega
  rw [hidx] at hc
  exact absurd hc (ne_of_gt (hpos (k + 1)))

/-- The vertex set of the summand shifted by `d`, for a general leg vector. -/
def vsetA (a : ℕ → ℝ) (N d n : ℕ) : Set (Fin N → ℝ) := (fun k => ravA a N d k) '' (Set.Icc 1 n)

lemma vsetA_finite (a : ℕ → ℝ) (N d n : ℕ) : (vsetA a N d n).Finite :=
  (Set.finite_Icc 1 n).image _

lemma ravA_mem_vsetA {a : ℕ → ℝ} {N d n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ravA a N d k ∈ vsetA a N d n := ⟨k, ⟨hk, hkn⟩, rfl⟩

/-- The `n` vertices of a shifted summand are distinct when the window fits, for any positive leg
vector.  Same argument as `rav_injOn`, generalised off the all-ones case. -/
lemma ravA_injOn (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {N d n : ℕ} (h : d + n ≤ N) :
    Set.InjOn (ravA a N d) (Set.Icc 1 n) := by
  intro k hk k' hk' hEq
  simp only [Set.mem_Icc] at hk hk'
  by_contra hne
  rcases Nat.lt_or_ge k k' with hlt | hge
  · have hb : d + k' - 1 < N := by omega
    have h1 := congrFun hEq (⟨d + k' - 1, hb⟩ : Fin N)
    simp only [ravA, Fin.val_mk] at h1
    rw [if_neg (by omega), if_pos (by omega)] at h1
    have hidx : d + k' - 1 + 1 - d = k' := by omega
    rw [hidx] at h1
    exact absurd h1.symm (ne_of_gt (hpos k'))
  · have hlt : k' < k := by omega
    have hb : d + k - 1 < N := by omega
    have h1 := congrFun hEq (⟨d + k - 1, hb⟩ : Fin N)
    simp only [ravA, Fin.val_mk] at h1
    rw [if_pos (by omega), if_neg (by omega)] at h1
    have hidx : d + k - 1 + 1 - d = k := by omega
    rw [hidx] at h1
    exact absurd h1 (ne_of_gt (hpos k))

/-- **`prop-adjacent`, geometrically.**  For any positive leg vector, the entry of the extremal
matrix immediately above the diagonal vanishes -- provided `j = t+1` stays inside the overlap block,
which is the hypothesis `d + t + 1 ≤ n`.  That hypothesis is exactly the qualifier the earlier
Proposition 47 omitted, and it is load-bearing here: it is what puts `t+1` in the index range
`[1,n]` of the second summand's vertices. -/
theorem prop_adjacent_upper_geom {n d t : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (ht : 1 ≤ t) (hd : 1 ≤ d) (hup : d + t + 1 ≤ n) :
    ravA a N 0 (d + t) + ravA a N d (t + 1) ∉
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) := by
  intro hmem
  rw [mem_extremePoints_add_iff (vsetA_finite a N 0 n) (vsetA_finite a N d n)
      (ravA_mem_vsetA (by omega) (by omega)) (ravA_mem_vsetA (by omega) (by omega))] at hmem
  obtain ⟨f, hS, hT⟩ := hmem
  refine prop_adjacent_upper a hpos hN ht hup f (fun k hk1 hkn hkne => ?_)
    (fun k hk1 hkn hkne => ?_)
  · exact hS _ (ravA_mem_vsetA hk1 hkn) (fun hc =>
      hkne (ravA_injOn a hpos (n := n) (by omega) ⟨hk1, hkn⟩ ⟨by omega, by omega⟩ hc))
  · exact hT _ (ravA_mem_vsetA hk1 hkn) (fun hc =>
      hkne (ravA_injOn a hpos (n := n) (by omega) ⟨hk1, hkn⟩ ⟨by omega, by omega⟩ hc))

/-! ## Unimodality from increments, and `prop-diagonal` -/

/-- Chaining strict increases along a run. -/
lemma chain_up {F : ℕ → ℝ} :
    ∀ (p k : ℕ), (∀ l, k ≤ l → l < p → F l < F (l + 1)) → k < p → F k < F p := by
  intro p
  induction p with
  | zero => intro k _ hk; omega
  | succ p ih =>
      intro k hup hk
      rcases Nat.lt_or_ge k p with h | h
      · exact lt_trans (ih k (fun l hl hlp => hup l hl (by omega)) h) (hup p (by omega) (by omega))
      · have hkp : k = p := by omega
        subst hkp
        exact hup k (le_refl _) (by omega)

/-- Chaining strict decreases along a run. -/
lemma chain_down {F : ℕ → ℝ} :
    ∀ (p k : ℕ), (∀ l, p ≤ l → l < k → F (l + 1) < F l) → p < k → F k < F p := by
  intro p k
  induction k with
  | zero => intro _ hk; omega
  | succ k ih =>
      intro hdown hk
      rcases Nat.lt_or_ge p k with h | h
      · exact lt_trans (hdown k (by omega) (by omega))
          (ih (fun l hl hlk => hdown l hl (by omega)) h)
      · have hkp : k = p := by omega
        subst hkp
        exact hdown k (by omega) (by omega)

/-- The threshold functional of `prop-diagonal`: `+1` on the manuscript's coordinates `1,…,p` and
`-1` beyond.  With `p = d + t` this is exactly the manuscript's choice -- `+1` on `[1,d]`, `+1` on
the shared block up to `s = t`, `-1` after, and `-1` on `[n+1,N]` -- written as one formula. -/
def wDiag (N p : ℕ) : Fin N → ℝ := fun c => if c.val + 1 ≤ p then 1 else -1

/-- One functional, both summands.  For the threshold `p`, the summand shifted by `d` has its
unique maximum at the vertex `q` with `d + q = p`.  Applying this with `d = 0`, `q = d + t` and with
shift `d`, `q = t` -- the same `p` both times -- is the whole of `prop-diagonal`. -/
lemma wDiag_unique_max {n d p q : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hq : d + q = p) (hqn : q ≤ n) (hbound : d + n ≤ N) :
    ∀ k, k ≤ n → k ≠ q →
      coeffCLM (wDiag N p) (ravA a N d k) < coeffCLM (wDiag N p) (ravA a N d q) := by
  set F : ℕ → ℝ := fun k => coeffCLM (wDiag N p) (ravA a N d k) with hF
  have hstep : ∀ l (hl : l < n),
      F (l + 1) = F l + a (l + 1) * wDiag N p ⟨d + l, by omega⟩ := by
    intro l hl
    simp only [hF]
    rw [map_ravA_succ (coeffCLM (wDiag N p)) a d l (by omega), coeffCLM_single]
  have hup : ∀ l, l < q → F l < F (l + 1) := by
    intro l hl
    rw [hstep l (by omega)]
    have : wDiag N p (⟨d + l, by omega⟩ : Fin N) = 1 := by
      simp only [wDiag]; rw [if_pos (by omega)]
    rw [this]
    nlinarith [hpos (l + 1)]
  have hdown : ∀ l, q ≤ l → l < n → F (l + 1) < F l := by
    intro l hl hln
    rw [hstep l hln]
    have : wDiag N p (⟨d + l, by omega⟩ : Fin N) = -1 := by
      simp only [wDiag]; rw [if_neg (by omega)]
    rw [this]
    nlinarith [hpos (l + 1)]
  intro k hk hkq
  rcases Nat.lt_or_ge k q with h | h
  · exact chain_up q k (fun l _ hl => hup l hl) h
  · exact chain_down q k (fun l hl hlk => hdown l hl (by omega)) (by omega)

/-- **`prop-diagonal`, geometrically.**  For any positive leg vector the diagonal entry of the
extremal matrix is one: `v_{d+t} + u_t` is a vertex of the Minkowski sum. -/
theorem prop_diagonal_geom {n d t : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (ht : 1 ≤ t) (htn : d + t ≤ n) :
    ravA a N 0 (d + t) + ravA a N d t ∈
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) := by
  rw [mem_extremePoints_add_iff (vsetA_finite a N 0 n) (vsetA_finite a N d n)
      (ravA_mem_vsetA (by omega) (by omega)) (ravA_mem_vsetA (by omega) (by omega))]
  refine ⟨coeffCLM (wDiag N (d + t)), ?_, ?_⟩
  · rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    exact wDiag_unique_max a hpos (by omega) (by omega) (by omega) k hk.2
      (fun hc => hne (by rw [hc]))
  · rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    exact wDiag_unique_max a hpos (by omega) (by omega) (by omega) k hk.2
      (fun hc => hne (by rw [hc]))

/-! ## Values as sums, and the two outside-the-block propositions -/

/-- The value of a coefficient functional along the vertices of one summand, as an explicit sum.
Coefficients are indexed by `ℕ` rather than `Fin N` so that the sum carries no dependent typing. -/
lemma value_eq_sum (wN : ℕ → ℝ) (a : ℕ → ℝ) (d k : ℕ) (hk : d + k ≤ N) :
    coeffCLM (fun c : Fin N => wN c.val) (ravA a N d k)
      = ∑ l ∈ Finset.range k, a (l + 1) * wN (d + l) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [map_ravA_succ (coeffCLM fun c : Fin N => wN c.val) a d k (by omega), ih (by omega),
        coeffCLM_single, Finset.sum_range_succ]

/-- A crude but sufficient bound: with coefficients at most `1` in absolute value, any partial sum
of increments is at most the total of all legs. -/
lemma sum_incr_le {wN : ℕ → ℝ} {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) (hw : ∀ l, wN l ≤ 1)
    {p q n : ℕ} (hq : q ≤ n) :
    ∑ l ∈ Finset.Ico p q, a (l + 1) * wN l ≤ ∑ l ∈ Finset.range n, a (l + 1) := by
  calc ∑ l ∈ Finset.Ico p q, a (l + 1) * wN l
      ≤ ∑ l ∈ Finset.Ico p q, a (l + 1) := by
        refine Finset.sum_le_sum (fun l _ => ?_)
        nlinarith [hpos (l + 1), hw l]
    _ ≤ ∑ l ∈ Finset.range n, a (l + 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l _ _ => (hpos (l + 1)).le)
        intro l hl
        simp only [Finset.mem_Ico] at hl
        exact Finset.mem_range.mpr (by omega)

/-- The coefficient vector of `prop-row-below`: `+1` up to `i`, `-1` on to `d`, then `-M` on the
*first shared coordinate*, then the `lem-shape` pattern peaking at `j`. -/
noncomputable def wRow (i d j : ℕ) (M : ℝ) : ℕ → ℝ := fun c =>
  if c < i then 1 else if c < d then -1 else if c = d then -M
  else if c + 1 ≤ d + j then 1 else -1

lemma wRow_le_one {i d j : ℕ} {M : ℝ} (hM : 0 ≤ M) (l : ℕ) : wRow i d j M l ≤ 1 := by
  simp only [wRow]
  split_ifs <;> linarith

/-- **`prop-row-below`, geometrically.**  For any positive leg vector, every entry in a row that
stops inside the first private block is one.  This is the case an earlier draft's proof did not
cover at `i = d`; the device is `-M` on the *first shared coordinate*, which pushes every
`Q_{t'}` below zero while shifting all of the second summand's values by the same constant. -/
theorem prop_row_below_geom {n d i j : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n) (hi : 1 ≤ i) (hid : i ≤ d)
    (hj : 1 ≤ j) (hjn : j ≤ n) :
    ravA a N 0 i + ravA a N d j ∈
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) := by
  set S : ℝ := ∑ l ∈ Finset.range n, a (l + 1) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun l _ => (hpos (l + 1)).le)
  set M : ℝ := (S + 1) / a (d + 1) with hM
  have hMpos : 0 < M := div_pos (by linarith) (hpos (d + 1))
  have hMa : M * a (d + 1) = S + 1 := by
    rw [hM, div_mul_cancel₀ _ (ne_of_gt (hpos (d + 1)))]
  set wN : ℕ → ℝ := wRow i d j M with hwN
  set f := coeffCLM (fun c : Fin N => wN c.val) with hf
  -- Values along each summand, as sums.
  have hval : ∀ (dd k : ℕ), dd + k ≤ N →
      f (ravA a N dd k) = ∑ l ∈ Finset.range k, a (l + 1) * wN (dd + l) :=
    fun dd k h => value_eq_sum wN a dd k h
  -- Coefficient values, unfolded once.
  have hw_lt : ∀ l, l < i → wN l = 1 := by
    intro l hl; simp only [hwN, wRow]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_mid : ∀ l, i ≤ l → l < d → wN l = -1 := by
    intro l h1 h2; simp only [hwN, wRow]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_d : wN d = -M := by
    simp only [hwN, wRow]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_up : ∀ l, d < l → l < d + j → wN l = 1 := by
    intro l h1 h2; simp only [hwN, wRow]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_dn : ∀ l, d + j ≤ l → wN l = -1 := by
    intro l h1; simp only [hwN, wRow]; split_ifs <;> first | rfl | (exfalso; omega)
  rw [mem_extremePoints_add_iff (vsetA_finite a N 0 n) (vsetA_finite a N d n)
      (ravA_mem_vsetA hi (by omega)) (ravA_mem_vsetA hj hjn)]
  refine ⟨f, ?_, ?_⟩
  · -- First summand: unique maximum at `i`.
    rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    have hki : k ≠ i := fun hc => hne (by rw [hc])
    set F : ℕ → ℝ := fun k => f (ravA a N 0 k) with hFdef
    have hstep : ∀ l (hl : l < n), F (l + 1) = F l + a (l + 1) * wN l := by
      intro l hl
      simp only [hFdef]
      rw [map_ravA_succ f a 0 l (by omega), hf, coeffCLM_single]
      simp
    have hup : ∀ l, l < i → F l < F (l + 1) := by
      intro l hl
      rw [hstep l (by omega), hw_lt l hl]; nlinarith [hpos (l + 1)]
    have hdown : ∀ l, i ≤ l → l < d → F (l + 1) < F l := by
      intro l h1 h2
      rw [hstep l (by omega), hw_mid l h1 h2]; nlinarith [hpos (l + 1)]
    have hle_d : F d ≤ F i := by
      rcases eq_or_lt_of_le hid with h | h
      · rw [h]
      · exact (chain_down i d (fun l hl hld => hdown l hl hld) h).le
    -- Beyond `d`, the `-M` coefficient dominates.
    have hbeyond : ∀ k, d < k → k ≤ n → F k < F d := by
      intro k hk1 hk2
      have e1 : F k = F d + ∑ l ∈ Finset.Ico d k, a (l + 1) * wN l := by
        rw [hFdef]
        simp only
        rw [hval 0 k (by omega), hval 0 d (by omega)]
        simp only [Nat.zero_add]
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le d) (le_of_lt hk1)]
      have e2 : ∑ l ∈ Finset.Ico d k, a (l + 1) * wN l
          = a (d + 1) * wN d + ∑ l ∈ Finset.Ico (d + 1) k, a (l + 1) * wN l :=
        Finset.sum_eq_sum_Ico_succ_bot hk1 _
      have e3 : ∑ l ∈ Finset.Ico (d + 1) k, a (l + 1) * wN l ≤ S :=
        sum_incr_le hpos (fun l => wRow_le_one hMpos.le l) hk2
      rw [e1, e2, hw_d]
      nlinarith [hpos (d + 1)]
    show F k < F i
    rcases Nat.lt_or_ge k i with h | h
    · exact chain_up i k (fun l _ hl => hup l hl) h
    · have hik : i < k := lt_of_le_of_ne h (Ne.symm hki)
      rcases Nat.lt_or_ge k (d + 1) with h2 | h2
      · refine chain_down i k ?_ hik
        intro l hl hlk
        exact hdown l hl (by omega)
      · exact lt_of_lt_of_le (hbeyond k (by omega) hk.2) hle_d
  · -- Second summand: unique maximum at `j`, whatever `M` is.
    rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    have hkj : k ≠ j := fun hc => hne (by rw [hc])
    set G : ℕ → ℝ := fun k => f (ravA a N d k) with hGdef
    have hstep : ∀ l (hl : l < n), G (l + 1) = G l + a (l + 1) * wN (d + l) := by
      intro l hl
      simp only [hGdef]
      rw [map_ravA_succ f a d l (by omega), hf, coeffCLM_single]
    have hup : ∀ l, 1 ≤ l → l < j → G l < G (l + 1) := by
      intro l h1 h2
      rw [hstep l (by omega), hw_up (d + l) (by omega) (by omega)]
      nlinarith [hpos (l + 1)]
    have hdown : ∀ l, j ≤ l → l < n → G (l + 1) < G l := by
      intro l h1 h2
      rw [hstep l h2, hw_dn (d + l) (by omega)]
      nlinarith [hpos (l + 1)]
    show G k < G j
    rcases Nat.lt_or_ge k j with h | h
    · refine chain_up j k ?_ h
      intro l hl hlj
      exact hup l (by omega) hlj
    · have hjk : j < k := lt_of_le_of_ne h (Ne.symm hkj)
      refine chain_down j k ?_ hjk
      intro l hl hlk
      exact hdown l hl (by omega)

/-- A two-sided bound on a partial sum of increments whose coefficients are bounded by one on the
range in question. -/
lemma abs_sum_incr_le {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {g : ℕ → ℝ} {p q n : ℕ} (hq : q ≤ n)
    (hg : ∀ l ∈ Finset.Ico p q, |g l| ≤ 1) :
    |∑ l ∈ Finset.Ico p q, a (l + 1) * g l| ≤ ∑ l ∈ Finset.range n, a (l + 1) := by
  calc |∑ l ∈ Finset.Ico p q, a (l + 1) * g l|
      ≤ ∑ l ∈ Finset.Ico p q, |a (l + 1) * g l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Ico p q, a (l + 1) := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        rw [abs_mul, abs_of_pos (hpos (l + 1))]
        nlinarith [hpos (l + 1), hg l hl, abs_nonneg (g l)]
    _ ≤ ∑ l ∈ Finset.range n, a (l + 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l _ _ => (hpos (l + 1)).le)
        intro l hl
        simp only [Finset.mem_Ico] at hl
        exact Finset.mem_range.mpr (by omega)

/-- The coefficient vector of `prop-col-beyond`: the `lem-shape` pattern peaking at `i` across
`[1,n]`, and `±Γ` on the second private block, positive exactly up to the coordinate `d+j`. -/
noncomputable def wCol (i n d j : ℕ) (G : ℝ) : ℕ → ℝ := fun c =>
  if c < n then (if c < i then 1 else -1) else (if c + 1 ≤ d + j then G else -G)

/-- **`prop-col-beyond`, geometrically.**  For any positive leg vector, every entry in a column that
reaches the second private block is one.  Here the second summand has room of its own, and a large
*positive* weight on it settles the matter -- a different construction from `prop-row-below`, which
is why the manuscript now states the two separately. -/
theorem prop_col_beyond_geom {n d i j : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n)
    (hj : n - d < j) (hjn : j ≤ n) :
    ravA a N 0 i + ravA a N d j ∈
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) := by
  set m := n - d with hm
  have hmj : m < j := hj
  set S : ℝ := ∑ l ∈ Finset.range n, a (l + 1) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun l _ => (hpos (l + 1)).le)
  set P : ℝ := ∑ l ∈ Finset.Ico m j, a (l + 1) with hP
  have hPpos : 0 < P := by
    refine Finset.sum_pos (fun l _ => hpos (l + 1)) ⟨m, Finset.mem_Ico.mpr ⟨le_refl _, hmj⟩⟩
  set Gam : ℝ := (S + 1) / P with hGam
  have hGampos : 0 < Gam := div_pos (by linarith) hPpos
  have hGamP : Gam * P = S + 1 := by rw [hGam, div_mul_cancel₀ _ (ne_of_gt hPpos)]
  set wN : ℕ → ℝ := wCol i n d j Gam with hwN
  set f := coeffCLM (fun c : Fin N => wN c.val) with hf
  have hval : ∀ (dd k : ℕ), dd + k ≤ N →
      f (ravA a N dd k) = ∑ l ∈ Finset.range k, a (l + 1) * wN (dd + l) :=
    fun dd k h => value_eq_sum wN a dd k h
  have hw_lo : ∀ l, l < n → l < i → wN l = 1 := by
    intro l h1 h2; simp only [hwN, wCol]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_hi : ∀ l, l < n → i ≤ l → wN l = -1 := by
    intro l h1 h2; simp only [hwN, wCol]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_up : ∀ l, n ≤ l → l < d + j → wN l = Gam := by
    intro l h1 h2; simp only [hwN, wCol]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_dn : ∀ l, n ≤ l → d + j ≤ l → wN l = -Gam := by
    intro l h1 h2; simp only [hwN, wCol]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw_abs : ∀ l, l < n → |wN l| ≤ 1 := by
    intro l hl
    rcases Nat.lt_or_ge l i with h | h
    · rw [hw_lo l hl h]; norm_num
    · rw [hw_hi l hl h]; norm_num
  rw [mem_extremePoints_add_iff (vsetA_finite a N 0 n) (vsetA_finite a N d n)
      (ravA_mem_vsetA hi hin) (ravA_mem_vsetA (by omega) hjn)]
  refine ⟨f, ?_, ?_⟩
  · rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    have hki : k ≠ i := fun hc => hne (by rw [hc])
    set F : ℕ → ℝ := fun k => f (ravA a N 0 k) with hFdef
    have hstep : ∀ l (hl : l < n), F (l + 1) = F l + a (l + 1) * wN l := by
      intro l hl
      simp only [hFdef]
      rw [map_ravA_succ f a 0 l (by omega), hf, coeffCLM_single]
      simp
    have hup : ∀ l, l < i → F l < F (l + 1) := by
      intro l hl
      rw [hstep l (by omega), hw_lo l (by omega) hl]; nlinarith [hpos (l + 1)]
    have hdown : ∀ l, i ≤ l → l < n → F (l + 1) < F l := by
      intro l h1 h2
      rw [hstep l h2, hw_hi l h2 h1]; nlinarith [hpos (l + 1)]
    show F k < F i
    rcases Nat.lt_or_ge k i with h | h
    · exact chain_up i k (fun l _ hl => hup l hl) h
    · have hik : i < k := lt_of_le_of_ne h (Ne.symm hki)
      refine chain_down i k ?_ hik
      intro l hl hlk
      exact hdown l hl (by omega)
  · rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    have hkj : k ≠ j := fun hc => hne (by rw [hc])
    set G : ℕ → ℝ := fun k => f (ravA a N d k) with hGdef
    have hstep : ∀ l (hl : l < n), G (l + 1) = G l + a (l + 1) * wN (d + l) := by
      intro l hl
      simp only [hGdef]
      rw [map_ravA_succ f a d l (by omega), hf, coeffCLM_single]
    have hup : ∀ l, m ≤ l → l < j → G l < G (l + 1) := by
      intro l h1 h2
      rw [hstep l (by omega), hw_up (d + l) (by omega) (by omega)]
      nlinarith [hpos (l + 1)]
    have hdown : ∀ l, j ≤ l → l < n → G (l + 1) < G l := by
      intro l h1 h2
      rw [hstep l h2, hw_dn (d + l) (by omega) (by omega)]
      nlinarith [hpos (l + 1)]
    have hjm : G j = G m + Gam * P := by
      have e1 : G j = G m + ∑ l ∈ Finset.Ico m j, a (l + 1) * wN (d + l) := by
        simp only [hGdef]
        rw [hval d j (by omega), hval d m (by omega), Finset.range_eq_Ico,
          Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) (le_of_lt hmj)]
      have e2 : ∑ l ∈ Finset.Ico m j, a (l + 1) * wN (d + l) = Gam * P := by
        rw [hP, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        simp only [Finset.mem_Ico] at hl
        rw [hw_up (d + l) (by omega) (by omega)]
        ring
      rw [e1, e2]
    have hbelow : ∀ k, k ≤ m → G k ≤ G m + S := by
      intro k hk
      have e1 : G m = G k + ∑ l ∈ Finset.Ico k m, a (l + 1) * wN (d + l) := by
        simp only [hGdef]
        rw [hval d m (by omega), hval d k (by omega), Finset.range_eq_Ico,
          Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hk]
      have e2 : |∑ l ∈ Finset.Ico k m, a (l + 1) * wN (d + l)| ≤ S := by
        have hb := abs_sum_incr_le (a := a) hpos (g := fun l => wN (d + l)) (p := k) (q := m)
          (n := n) (by omega) (fun l hl => by
            simp only [Finset.mem_Ico] at hl
            exact hw_abs (d + l) (by omega))
        simpa [hS] using hb
      have h3 := (abs_le.mp e2).1
      linarith [e1.ge, e1.le]
    show G k < G j
    rcases Nat.lt_or_ge k m with h | h
    · have h1 : G k ≤ G m + S := hbelow k (by omega)
      calc G k ≤ G m + S := h1
        _ < G m + Gam * P := by rw [hGamP]; linarith
        _ = G j := hjm.symm
    · rcases Nat.lt_or_ge k j with h2 | h2
      · exact chain_up j k (fun l hl hlj => hup l (by omega) hlj) h2
      · have hjk : j < k := lt_of_le_of_ne h2 (Ne.symm hkj)
        refine chain_down j k ?_ hjk
        intro l hl hlk
        exact hdown l hl (by omega)

/-! ## `prop-below-diagonal`: summation by parts -/

/-- The coefficient a functional assigns to a coordinate, as a total function on `ℕ`. -/
noncomputable def coefAt (f : (Fin N → ℝ) →L[ℝ] ℝ) (c : ℕ) : ℝ :=
  if h : c < N then f (Pi.single ⟨c, h⟩ 1) else 0

lemma map_ravA_succ' (f : (Fin N → ℝ) →L[ℝ] ℝ) (a : ℕ → ℝ) (d k : ℕ) (h : d + k < N) :
    f (ravA a N d (k + 1)) = f (ravA a N d k) + a (k + 1) * coefAt f (d + k) := by
  rw [map_ravA_succ f a d k h, coefAt, dif_pos h]

/-- The increase of a functional along a stretch of vertices, as a sum of increments. -/
lemma value_diff_eq_sum (f : (Fin N → ℝ) →L[ℝ] ℝ) (a : ℕ → ℝ) (d p : ℕ) :
    ∀ q, p ≤ q → d + q ≤ N →
      f (ravA a N d q) = f (ravA a N d p) + ∑ l ∈ Finset.Ico p q, a (l + 1) * coefAt f (d + l) := by
  intro q
  induction q with
  | zero => intro hpq _; simp [Nat.le_zero.mp hpq]
  | succ q ih =>
      intro hpq hq
      rcases Nat.lt_or_ge p (q + 1) with h | h
      · have hpq' : p ≤ q := by omega
        rw [map_ravA_succ' f a d q (by omega), ih hpq' (by omega),
          Finset.sum_Ico_succ_top hpq']
        ring
      · have : p = q + 1 := by omega
        subst this
        simp

/-- Summation by parts, in the form the manuscript uses: `B` are the partial sums of the increments
and `R` the ratios, with `B 0 = 0`. -/
lemma abel_sum (B R : ℕ → ℝ) (h0 : B 0 = 0) : ∀ K : ℕ,
    ∑ s ∈ Finset.range K, (B (s + 1) - B s) * R (s + 1)
      = B K * R K + ∑ s ∈ Finset.range K, B s * (R s - R (s + 1)) := by
  intro K
  induction K with
  | zero => simp [h0]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- **`prop-below-diagonal`.**  No functional can expose `v_{d+t}` and `u_j` together when `j < t`,
provided the ratios `ρ` are strictly decreasing across the gap.  This is the one short case that
needs more of the leg vector than positivity, and the argument is summation by parts. -/
theorem prop_below_diagonal {n d t j : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (ht : 1 ≤ t) (htn : d + t ≤ n) (hj : 1 ≤ j) (hjt : j < t)
    (hrho : ∀ s, j ≤ s → s + 2 ≤ t → a (d + s + 1) / a (s + 1) > a (d + s + 2) / a (s + 2))
    (f : (Fin N → ℝ) →L[ℝ] ℝ)
    (h₁ : ∀ k, 1 ≤ k → k ≤ n → k ≠ d + t → f (ravA a N 0 k) < f (ravA a N 0 (d + t)))
    (h₂ : ∀ k, 1 ≤ k → k ≤ n → k ≠ j → f (ravA a N d k) < f (ravA a N d j)) :
    False := by
  set K := t - j with hK
  have hKpos : 0 < K := by omega
  -- `B s` is the gain of the second summand from `u_j` to `u_{j+s}`; every one is negative.
  set B : ℕ → ℝ := fun s => f (ravA a N d (j + s)) - f (ravA a N d j) with hB
  have hB0 : B 0 = 0 := by simp [hB]
  have hBneg : ∀ s, 1 ≤ s → s ≤ K → B s < 0 := by
    intro s h1 h2
    have := h₂ (j + s) (by omega) (by omega) (by omega)
    simp only [hB]
    linarith
  -- `R s` is the ratio at the coordinate reached by step `s`.
  set R : ℕ → ℝ := fun s => a (d + j + s) / a (j + s) with hR
  have hRpos : ∀ s, 0 < R s := fun s => div_pos (hpos _) (hpos _)
  have hRdec : ∀ s, 1 ≤ s → s < K → R s > R (s + 1) := by
    intro s h1 h2
    have := hrho (j + s - 1) (by omega) (by omega)
    have e1 : d + (j + s - 1) + 1 = d + j + s := by omega
    have e2 : j + s - 1 + 1 = j + s := by omega
    have e3 : d + (j + s - 1) + 2 = d + j + (s + 1) := by omega
    have e4 : j + s - 1 + 2 = j + (s + 1) := by omega
    rw [e1, e2, e3, e4] at this
    simpa [hR] using this
  -- The increments of `B`, and the same increments weighted by `R`, which is what the first
  -- summand sees.
  have hstepB : ∀ s, s < K → B (s + 1) - B s = a (j + s + 1) * coefAt f (d + (j + s)) := by
    intro s hs
    simp only [hB]
    have := map_ravA_succ' f a d (j + s) (show d + (j + s) < N by omega)
    have e : j + (s + 1) = j + s + 1 := by omega
    rw [e, this]
    ring
  -- The first summand's requirement, expanded.
  have hfirst : 0 < ∑ s ∈ Finset.range K, (B (s + 1) - B s) * R (s + 1) := by
    have hlt := h₁ (d + j) (by omega) (by omega) (by omega)
    have hsum := value_diff_eq_sum f a 0 (d + j) (d + t) (by omega) (by omega)
    have e : ∑ l ∈ Finset.Ico (d + j) (d + t), a (l + 1) * coefAt f (0 + l)
        = ∑ s ∈ Finset.range K, (B (s + 1) - B s) * R (s + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have e2 : d + t - (d + j) = K := by omega
      rw [e2]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      simp only [Finset.mem_range] at hs
      rw [hstepB s hs]
      have e3 : d + j + s + 1 = d + (j + s) + 1 := by omega
      have e4 : R (s + 1) = a (d + j + (s + 1)) / a (j + (s + 1)) := rfl
      rw [Nat.zero_add, e3, e4]
      have e5 : j + (s + 1) = j + s + 1 := by omega
      have e6 : d + j + (s + 1) = d + (j + s) + 1 := by omega
      have e7 : d + j + s = d + (j + s) := by omega
      rw [e5, e6, e7]
      have hne : a (j + s + 1) ≠ 0 := ne_of_gt (hpos (j + s + 1))
      field_simp
    rw [← e]
    linarith [hsum]
  -- Summation by parts makes the same quantity manifestly negative.
  have hneg : ∑ s ∈ Finset.range K, (B (s + 1) - B s) * R (s + 1) < 0 := by
    rw [abel_sum B R hB0 K]
    have hBK : B K * R K < 0 := mul_neg_of_neg_of_pos (hBneg K hKpos (le_refl _)) (hRpos K)
    have hrest : ∑ s ∈ Finset.range K, B s * (R s - R (s + 1)) ≤ 0 := by
      refine Finset.sum_nonpos (fun s hs => ?_)
      simp only [Finset.mem_range] at hs
      rcases Nat.eq_zero_or_pos s with rfl | hs1
      · rw [hB0]; simp
      · exact mul_nonpos_of_nonpos_of_nonneg (hBneg s hs1 (by omega)).le
          (by linarith [hRdec s hs1 hs])
    linarith
  linarith

/-! ## `prop-gapK`: the explicit functional -/

/-- Chaining equalities along a run. -/
lemma chain_const {F : ℕ → ℝ} :
    ∀ (p k : ℕ), (∀ l, p ≤ l → l < k → F (l + 1) = F l) → p ≤ k → F k = F p := by
  intro p k
  induction k with
  | zero => intro _ hk; rw [Nat.le_zero.mp hk]
  | succ k ih =>
      intro hc hk
      rcases Nat.lt_or_ge p (k + 1) with h | h
      · have hpk : p ≤ k := by omega
        rw [hc k hpk (by omega), ih (fun l hl hlk => hc l hl (by omega)) hpk]
      · have : p = k + 1 := by omega
        rw [this]

/-- The coefficient vector of `prop-gapK`, written out in one formula.  In the manuscript's terms:
`+1` on `[1,d]` and on the shared block up to `s = t`; `-1/a_{t+1}` at `s = t+1`; zero strictly
between; `(1+δ)/a_j` at `s = j`; and `-1` after that and on the second private block.  The two
private blocks carry `±1` exactly -- no largeness anywhere. -/
noncomputable def wGap (a : ℕ → ℝ) (d t j : ℕ) (dl : ℝ) : ℕ → ℝ := fun c =>
  if c < d + t then 1
  else if c = d + t then -1 / a (t + 1)
  else if c + 1 < d + j then 0
  else if c + 1 = d + j then (1 + dl) / a j
  else -1

/-- **`prop-gapK`, geometrically.**  When the gap `j - t` is at least two and the ratio at the near
end of the gap exceeds the ratio at the far end, `v_{d+t} + u_j` is a vertex.  The functional is
completely explicit; in particular no parameter has to be taken large. -/
theorem prop_gapK_geom {n d t j : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (ht : 1 ≤ t) (hj : t + 2 ≤ j) (hjm : d + j ≤ n)
    (hrho : a (d + j) / a j < a (d + t + 1) / a (t + 1)) :
    ravA a N 0 (d + t) + ravA a N d j ∈
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) := by
  set A1 : ℝ := a (d + t + 1) / a (t + 1) with hA1
  set A2 : ℝ := a (d + j) / a j with hA2
  have hA2pos : 0 < A2 := div_pos (hpos _) (hpos _)
  have hA1pos : 0 < A1 := lt_trans hA2pos hrho
  set dl : ℝ := (A1 / A2 - 1) / 2 with hdl
  have hdlpos : 0 < dl := by
    rw [hdl]
    have : 1 < A1 / A2 := (one_lt_div hA2pos).mpr hrho
    linarith
  -- The key identity: `(1+δ)·A₂` is the midpoint of `A₂` and `A₁`, hence below `A₁`.
  have hmid : (1 + dl) * A2 = (A1 + A2) / 2 := by
    rw [hdl]; field_simp; ring
  have hlt : (1 + dl) * A2 < A1 := by rw [hmid]; linarith
  set wN : ℕ → ℝ := wGap a d t j dl with hwN
  set f := coeffCLM (fun c : Fin N => wN c.val) with hf
  -- The five coefficient values.
  have hw1 : ∀ c, c < d + t → wN c = 1 := by
    intro c hc; simp only [hwN, wGap]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw2 : wN (d + t) = -1 / a (t + 1) := by
    simp only [hwN, wGap]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw3 : ∀ c, d + t < c → c + 1 < d + j → wN c = 0 := by
    intro c h1 h2; simp only [hwN, wGap]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw4 : ∀ c, c + 1 = d + j → wN c = (1 + dl) / a j := by
    intro c hc; simp only [hwN, wGap]; split_ifs <;> first | rfl | (exfalso; omega)
  have hw5 : ∀ c, d + j ≤ c → wN c = -1 := by
    intro c hc; simp only [hwN, wGap]; split_ifs <;> first | rfl | (exfalso; omega)
  rw [mem_extremePoints_add_iff (vsetA_finite a N 0 n) (vsetA_finite a N d n)
      (ravA_mem_vsetA (by omega) (by omega)) (ravA_mem_vsetA (by omega) (by omega))]
  refine ⟨f, ?_, ?_⟩
  · -- First summand: unique maximum at `d + t`.
    rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    have hki : k ≠ d + t := fun hc => hne (by rw [hc])
    set F : ℕ → ℝ := fun k => f (ravA a N 0 k) with hFdef
    have hstep : ∀ l (hl : l < n), F (l + 1) = F l + a (l + 1) * wN l := by
      intro l hl
      simp only [hFdef]
      rw [map_ravA_succ f a 0 l (by omega), hf, coeffCLM_single]
      simp
    have hup : ∀ l, l < d + t → F l < F (l + 1) := by
      intro l hl
      rw [hstep l (by omega), hw1 l hl]; nlinarith [hpos (l + 1)]
    have hdrop : F (d + t + 1) = F (d + t) - A1 := by
      rw [hstep (d + t) (by omega), hw2, hA1]
      ring
    have hflat : ∀ l, d + t + 1 ≤ l → l + 1 < d + j → F (l + 1) = F l := by
      intro l h1 h2
      rw [hstep l (by omega), hw3 l (by omega) h2]; ring
    have hplateau : ∀ l, d + t + 1 ≤ l → l + 1 ≤ d + j → F l = F (d + t + 1) := by
      intro l h1 h2
      exact chain_const (d + t + 1) l (fun c hc hcl => hflat c hc (by omega)) h1
    have hrise : F (d + j) = F (d + t + 1) + (1 + dl) * A2 := by
      have hprev : d + j = (d + j - 1) + 1 := by omega
      rw [hprev, hstep (d + j - 1) (by omega), hw4 (d + j - 1) (by omega),
        hplateau (d + j - 1) (by omega) (by omega)]
      have hidx : d + j - 1 + 1 = d + j := by omega
      rw [hidx, hA2]
      ring
    have hdown : ∀ l, d + j ≤ l → l < n → F (l + 1) < F l := by
      intro l h1 h2
      rw [hstep l h2, hw5 l h1]; nlinarith [hpos (l + 1)]
    have hFj : F (d + j) < F (d + t) := by
      rw [hrise, hdrop]; linarith
    show F k < F (d + t)
    rcases Nat.lt_or_ge k (d + t) with h | h
    · exact chain_up (d + t) k (fun l _ hl => hup l hl) h
    · have hgt : d + t < k := lt_of_le_of_ne h (Ne.symm hki)
      rcases Nat.lt_or_ge k (d + j) with h2 | h2
      · rw [hplateau k (by omega) (by omega), hdrop]; linarith
      · rcases eq_or_lt_of_le h2 with h3 | h3
        · exact h3 ▸ hFj
        · exact lt_trans (chain_down (d + j) k (fun l hl hlk => hdown l hl (by omega)) h3) hFj
  · -- Second summand: unique maximum at `j`.
    rintro y ⟨k, hk, rfl⟩ hne
    simp only [Set.mem_Icc] at hk
    have hkj : k ≠ j := fun hc => hne (by rw [hc])
    set G : ℕ → ℝ := fun k => f (ravA a N d k) with hGdef
    have hstep : ∀ l (hl : l < n), G (l + 1) = G l + a (l + 1) * wN (d + l) := by
      intro l hl
      simp only [hGdef]
      rw [map_ravA_succ f a d l (by omega), hf, coeffCLM_single]
    have hup : ∀ l, l < t → G l < G (l + 1) := by
      intro l hl
      rw [hstep l (by omega), hw1 (d + l) (by omega)]; nlinarith [hpos (l + 1)]
    have hdrop : G (t + 1) = G t - 1 := by
      rw [hstep t (by omega), hw2]
      have hne : a (t + 1) ≠ 0 := ne_of_gt (hpos (t + 1))
      field_simp
      ring
    have hflat : ∀ l, t + 1 ≤ l → l < j - 1 → G (l + 1) = G l := by
      intro l h1 h2
      rw [hstep l (by omega), hw3 (d + l) (by omega) (by omega)]; ring
    have hplateau : ∀ l, t + 1 ≤ l → l ≤ j - 1 → G l = G (t + 1) := by
      intro l h1 h2
      exact chain_const (t + 1) l (fun c hc hcl => hflat c hc (by omega)) h1
    have hrise : G j = G (t + 1) + (1 + dl) := by
      have hprev : j = (j - 1) + 1 := by omega
      rw [hprev, hstep (j - 1) (by omega), hw4 (d + (j - 1)) (by omega),
        hplateau (j - 1) (by omega) (by omega)]
      have hidx : a (j - 1 + 1) = a j := by rw [show j - 1 + 1 = j from by omega]
      rw [hidx]
      have hne : a j ≠ 0 := ne_of_gt (hpos j)
      field_simp
    have hdown : ∀ l, j ≤ l → l < n → G (l + 1) < G l := by
      intro l h1 h2
      rw [hstep l h2, hw5 (d + l) (by omega)]; nlinarith [hpos (l + 1)]
    have hGt : G t < G j := by rw [hrise, hdrop]; linarith
    show G k < G j
    rcases Nat.lt_or_ge k t with h | h
    · exact lt_trans (chain_up t k (fun l _ hl => hup l hl) h) hGt
    · rcases eq_or_lt_of_le h with h2 | h2
      · exact h2 ▸ hGt
      · rcases Nat.lt_or_ge k j with h3 | h3
        · rw [hplateau k (by omega) (by omega), hrise, hdrop]; linarith
        · have hjk : j < k := lt_of_le_of_ne h3 (Ne.symm hkj)
          refine chain_down j k ?_ hjk
          intro l hl hlk
          exact hdown l hl (by omega)

/-! ## Assembly: the extremal matrix -/

/-- Turning a "no functional can do both" lemma into non-membership. -/
lemma not_mem_of_no_functional {n d i j : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (H : ∀ f : (Fin N → ℝ) →L[ℝ] ℝ,
      (∀ k, 1 ≤ k → k ≤ n → k ≠ i → f (ravA a N 0 k) < f (ravA a N 0 i)) →
      (∀ k, 1 ≤ k → k ≤ n → k ≠ j → f (ravA a N d k) < f (ravA a N d j)) → False) :
    ravA a N 0 i + ravA a N d j ∉
      Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n)) := by
  intro hmem
  rw [mem_extremePoints_add_iff (vsetA_finite a N 0 n) (vsetA_finite a N d n)
      (ravA_mem_vsetA hi hin) (ravA_mem_vsetA hj hjn)] at hmem
  obtain ⟨f, hS, hT⟩ := hmem
  refine H f (fun k hk1 hkn hkne => ?_) (fun k hk1 hkn hkne => ?_)
  · exact hS _ (ravA_mem_vsetA hk1 hkn) (fun hc =>
      hkne (ravA_injOn a hpos (n := n) (by omega) ⟨hk1, hkn⟩ ⟨hi, hin⟩ hc))
  · exact hT _ (ravA_mem_vsetA hk1 hkn) (fun hc =>
      hkne (ravA_injOn a hpos (n := n) (by omega) ⟨hk1, hkn⟩ ⟨hj, hjn⟩ hc))

/-- The ratio sequence of §8.3. -/
noncomputable def rho (a : ℕ → ℝ) (d s : ℕ) : ℝ := a (d + s) / a s

/-- Strict decrease of `rho` propagates across a gap. -/
lemma rho_lt_of_lt {a : ℕ → ℝ} {d m p q : ℕ}
    (hdec : ∀ s, 1 ≤ s → s < m → rho a d (s + 1) < rho a d s)
    (hp : 1 ≤ p) (hpq : p < q) (hq : q ≤ m) : rho a d q < rho a d p := by
  exact chain_down (F := fun s => rho a d s) p q
    (fun l hl hlq => hdec l (by omega) (by omega)) hpq

/-- **`thm-kozlov-matrix`.**  The full classification of the extremal matrix at rank two, for any
positive leg vector whose ratios decrease strictly across the overlap block -- which by
`ExteriorConvex.choose_ratio_lt` includes the Kozlov vector.  The zero set is exactly the
manuscript's: `1 ≤ t ≤ m`, `1 ≤ j ≤ m`, and `j < t` or `j = t + 1`. -/
theorem extremal_matrix_iff {n d i j : ℕ} (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s)
    (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hdec : ∀ s, 1 ≤ s → s < n - d → rho a d (s + 1) < rho a d s)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ravA a N 0 i + ravA a N d j ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N d n))
      ↔ ¬(d + 1 ≤ i ∧ j ≤ n - d ∧ (j + d < i ∨ i + 1 = d + j)) := by
  constructor
  · -- A vertex cannot sit on the zero set.
    intro hmem hzero
    obtain ⟨hid, hjm, hcase⟩ := hzero
    obtain ⟨t, rfl⟩ : ∃ t, i = d + t := ⟨i - d, by omega⟩
    rcases hcase with hlt | heq
    · exact not_mem_of_no_functional a hpos hN (by omega) hin hj hjn
        (fun f h₁ h₂ => prop_below_diagonal a hpos hN hd (by omega) (by omega) hj (by omega)
          (fun s hs1 hs2 => by
            have hstep := hdec (s + 1) (by omega) (by omega)
            simp only [rho] at hstep
            have e1 : d + (s + 1) = d + s + 1 := by omega
            have e2 : d + (s + 1 + 1) = d + s + 2 := by omega
            have e3 : s + 1 + 1 = s + 2 := by omega
            rw [e1, e2, e3] at hstep
            exact hstep) f h₁ h₂) hmem
    · exact not_mem_of_no_functional a hpos hN (by omega) hin hj hjn
        (fun f h₁ h₂ => prop_adjacent_upper a hpos hN (by omega) (by omega) f h₁
          (by rw [show j = t + 1 from by omega] at h₂; exact h₂)) hmem
  · -- Off the zero set, one of the four constructions applies.
    intro hoff
    rcases Nat.lt_or_ge i (d + 1) with hid | hid
    · exact prop_row_below_geom a hpos hN hd hdn hi (by omega) hj hjn
    · rcases Nat.lt_or_ge (n - d) j with hjm | hjm
      · exact prop_col_beyond_geom a hpos hN hd hdn hi hin hjm hjn
      · obtain ⟨t, rfl⟩ : ∃ t, i = d + t := ⟨i - d, by omega⟩
        have ht : 1 ≤ t := by omega
        push Not at hoff
        have hne1 : ¬(j + d < d + t) := fun hc => by
          exact absurd (hoff (by omega) hjm) (by simp [hc])
        have hne2 : ¬(d + t + 1 = d + j) := fun hc => by
          exact absurd (hoff (by omega) hjm) (by simp [hc])
        rcases Nat.lt_or_ge j t with h | h
        · exact absurd (by omega : j + d < d + t) hne1
        · rcases eq_or_lt_of_le h with h2 | h2
          · rw [← h2]
            exact prop_diagonal_geom a hpos hN hd ht (by omega)
          · have hj2 : t + 2 ≤ j := by omega
            refine prop_gapK_geom a hpos hN hd ht hj2 (by omega) ?_
            have := rho_lt_of_lt (a := a) (d := d) (m := n - d) hdec (by omega) hj2 (by omega)
            simpa [rho, Nat.add_assoc] using this


/-- The Kozlov leg vector, truncated to `1` above `n` so that it is positive everywhere.  `ravA`
only ever reads it at indices in `[1,n]`, so the truncation changes no polytope. -/
noncomputable def kozLeg (n : ℕ) : ℕ → ℝ := fun s => if s ≤ n then (n.choose s : ℝ) else 1

lemma kozLeg_pos (n : ℕ) : ∀ s, 0 < kozLeg n s := by
  intro s
  simp only [kozLeg]
  split_ifs with h
  · exact_mod_cast Nat.choose_pos h
  · norm_num

/-- **`thm-kozlov-matrix` for the Kozlov vector itself.**  Combining `extremal_matrix_iff` with
`ExteriorConvex.choose_ratio_lt`, which is `lem-binomial-ratio`. -/
theorem extremal_matrix_kozlov {n d i j : ℕ} (hN : N = n + d) (hd : 1 ≤ d) (hdn : d + 1 ≤ n)
    (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ravA (kozLeg n) N 0 i + ravA (kozLeg n) N d j ∈
        Set.extremePoints ℝ
          (convexHull ℝ (vsetA (kozLeg n) N 0 n) + convexHull ℝ (vsetA (kozLeg n) N d n))
      ↔ ¬(d + 1 ≤ i ∧ j ≤ n - d ∧ (j + d < i ∨ i + 1 = d + j)) := by
  refine extremal_matrix_iff _ (kozLeg_pos n) hN hd hdn ?_ hi hin hj hjn
  intro s hs1 hs2
  have e : d + (s + 1) = d + s + 1 := by omega
  simp only [rho, kozLeg, e]
  rw [if_pos (show d + s + 1 ≤ n by omega), if_pos (show s + 1 ≤ n by omega),
    if_pos (show d + s ≤ n by omega), if_pos (show s ≤ n by omega)]
  exact choose_ratio_lt hd hs1 (by omega)

end ExteriorConvex
