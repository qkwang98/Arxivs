/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung B of the article-2 formalisation: Alexander duality and `prop-fnn2`

Formalisation of `lem-alexander`, `cor-persymmetry` and `prop-fnn2` from
`article/exterior-convex_article2_draft_3.org`, per
`working-notes/PLAN-formalise-article2.org` (rung B).

* `dualIdeal Δ = {σ : [n]∖σ ∉ Δ}` is the Alexander dual, an order ideal
  again, with `dualIdeal (dualIdeal Δ) = Δ` (for *every* family, order
  ideal or not — double complementation asks nothing of `Δ`).
* `fEntry_dualIdeal_add` is `eq:alexander-f` in ℕ-safe additive form:
  `f_j(Δ^∨) + f_{n−j}(Δ) = C(n,j)`.
* `Dvec s⃗ = (j ↦ C(n,j) − s(n−j))` is the induced involution `D` of
  `𝓕_n`; `indeg_Dvec`/`top_Dvec` are `eq:alexander-stats`, the statistic
  conjugation `indeg(D s⃗) = n − tp(s⃗)` and `tp(D s⃗) = n − indeg(s⃗)`.
  **Both hold for arbitrary `s⃗ : Fin (n+1) → ℕ`**, not only on `𝓕_n` —
  a mild strengthening that truncated ℕ-subtraction hands over for free.
  Only the involution `Dvec (Dvec s⃗) = s⃗` needs the entrywise bound
  `s(j) ≤ C(n,j)`.
* `Amat_persymmetric` is `cor-persymmetry`, for all integer indices.
* `card_SnF_eq_Fcount` is `prop-fnn2`: `|S_n| = F^n(n−2)` for `n ≥ 1`,
  where `Fcount n m = #{s⃗ ∈ 𝓕_n : tp(s⃗) ≤ m}` is Linusson's `F^n(m)`
  **by counting** (`def-linusson` at `p = n`, where `f₁ ≤ n` is
  automatic) — the definition of record here, per the plan; the recursion
  is never mentioned.

The boundary conventions of `def-stats` (`tp = −1` for the void family,
`indeg = n+1` for the full simplex) are exactly what make `D` exchange
the two degenerate members of `𝓕_n`, which is why `𝓕_n` must be
convention (i): with either one removed, `D` would only be a partial map.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`).
-/
import ExteriorConvex.Counting.Stats

open Finset

namespace ExteriorConvex

variable {n : ℕ}

/-! ## The Alexander dual of a family -/

/-- `lem-alexander`: the Alexander dual `Δ^∨ = {σ : [n]∖σ ∉ Δ}`. -/
def dualIdeal (D : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter fun σ => σᶜ ∉ D

@[simp] theorem mem_dualIdeal {D : Finset (Finset (Fin n))}
    {σ : Finset (Fin n)} : σ ∈ dualIdeal D ↔ σᶜ ∉ D := by
  simp [dualIdeal]

/-- `lem-alexander`, first claim: the dual of an order ideal is an order
ideal. -/
theorem IsOrderIdeal.dual {D : Finset (Finset (Fin n))}
    (hD : IsOrderIdeal D) : IsOrderIdeal (dualIdeal D) := by
  intro σ τ hσ hτσ
  rw [mem_dualIdeal] at hσ ⊢
  intro hmem
  have hcompl : σᶜ ⊆ τᶜ := fun x hx => by
    rw [Finset.mem_compl] at hx ⊢
    exact fun hxτ => hx (hτσ hxτ)
  exact hσ (hD hmem hcompl)

/-- `lem-alexander`, second claim: duality is an involution — of the
whole power set of families; no order-ideal hypothesis is needed. -/
@[simp] theorem dualIdeal_dualIdeal (D : Finset (Finset (Fin n))) :
    dualIdeal (dualIdeal D) = D := by
  ext σ
  simp

/-! ## `eq:alexander-f`: the effect on `f`-vectors -/

/-- `eq:alexander-f` in additive (ℕ-safe) form:
`f_j(Δ^∨) + f_{n−j}(Δ) = C(n,j)`.  True for every family `Δ`. -/
theorem fEntry_dualIdeal_add (D : Finset (Finset (Fin n))) {j : ℕ}
    (hj : j ≤ n) :
    fEntry (dualIdeal D) j + fEntry D (n - j) = n.choose j := by
  -- the `j`-faces of the dual, transported by complementation
  have h1 : fEntry (dualIdeal D) j =
      #(univ.filter fun τ : Finset (Fin n) => #τ = n - j ∧ τ ∉ D) := by
    rw [fEntry]
    have hset : (dualIdeal D).filter (fun σ => #σ = j) =
        univ.filter fun σ : Finset (Fin n) => #σ = j ∧ σᶜ ∉ D := by
      ext σ
      simp [dualIdeal, and_comm]
    rw [hset]
    refine card_bij' (fun σ _ => σᶜ) (fun τ _ => τᶜ) ?_ ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨-, hcard, hnot⟩ := mem_filter.mp hσ
      refine mem_filter.mpr ⟨mem_univ _, ?_, hnot⟩
      rw [card_compl, hcard, Fintype.card_fin]
    · intro τ hτ
      obtain ⟨-, hcard, hnot⟩ := mem_filter.mp hτ
      refine mem_filter.mpr ⟨mem_univ _, ?_, by simpa using hnot⟩
      rw [card_compl, hcard, Fintype.card_fin]
      omega
    · intro σ _
      exact compl_compl σ
    · intro τ _
      exact compl_compl τ
  -- the `(n−j)`-faces of `Δ` itself, relative to the universe
  have h2 : fEntry D (n - j) =
      #(univ.filter fun τ : Finset (Fin n) => #τ = n - j ∧ τ ∈ D) := by
    rw [fEntry]
    congr 1
    ext τ
    simp [and_comm]
  -- the two counts partition the `(n−j)`-subsets of `[n]`
  have h3 : #(univ.filter fun τ : Finset (Fin n) => #τ = n - j) =
      n.choose (n - j) := fEntry_univ (n - j)
  rw [h1, h2, ← Nat.choose_symm hj, ← h3, ← filter_filter, ← filter_filter,
    add_comm]
  exact card_filter_add_card_filter_not (fun τ => τ ∈ D)

/-- `eq:alexander-f` in subtraction form. -/
theorem fEntry_dualIdeal (D : Finset (Finset (Fin n))) {j : ℕ}
    (hj : j ≤ n) :
    fEntry (dualIdeal D) j = n.choose j - fEntry D (n - j) := by
  have h := fEntry_dualIdeal_add D hj
  omega

/-! ## The involution `D` on `f`-vectors -/

/-- `lem-alexander`: the duality on `f`-vectors,
`(D s⃗)(j) = C(n,j) − s(n−j)`. -/
def Dvec (s : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ :=
  fun j => n.choose j.val - s j.rev

@[simp] theorem Dvec_apply (s : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    Dvec s j = n.choose j.val - s j.rev := rfl

/-- `rev` on `Fin (n+1)` preserves the binomial coefficient:
`C(n, n−j) = C(n,j)`. -/
theorem choose_rev_val (j : Fin (n + 1)) :
    n.choose j.rev.val = n.choose j.val := by
  have h : j.rev.val = n - j.val := by
    rw [Fin.val_rev]
    omega
  rw [h, Nat.choose_symm j.is_le]

/-- `D` intertwines Alexander duality of families with duality of their
`f`-vectors; in particular `D s⃗` depends only on `s⃗`. -/
theorem fvecN_dualIdeal (D : Finset (Finset (Fin n))) :
    fvecN (dualIdeal D) = Dvec (fvecN D) := by
  funext j
  simp only [fvecN_apply, Dvec_apply]
  rw [fEntry_dualIdeal D j.is_le]
  have h : j.rev.val = n - j.val := by
    rw [Fin.val_rev]
    omega
  rw [h]

/-- `lem-alexander`: `D` maps `𝓕_n` into itself. -/
theorem Dvec_mem_Fn {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n) :
    Dvec s ∈ Fn n := by
  obtain ⟨D, hD, rfl⟩ := mem_Fn.mp hs
  exact mem_Fn.mpr ⟨dualIdeal D, hD.dual, fvecN_dualIdeal D⟩

/-- `D` is an involution on entrywise-bounded vectors. -/
theorem Dvec_Dvec {s : Fin (n + 1) → ℕ}
    (hs : ∀ j, s j ≤ n.choose j.val) : Dvec (Dvec s) = s := by
  funext j
  have h1 : n.choose j.rev.val = n.choose j.val := choose_rev_val j
  have h2 := hs j
  simp only [Dvec_apply, Fin.rev_rev]
  omega

/-- `lem-alexander`: `D` is an involution of `𝓕_n`. -/
theorem Dvec_Dvec_of_mem_Fn {s : Fin (n + 1) → ℕ} (hs : s ∈ Fn n) :
    Dvec (Dvec s) = s :=
  Dvec_Dvec fun j => apply_le_choose_of_mem_Fn hs j

/-! ## `eq:alexander-stats`: the statistic conjugation

Two helper facts: `rev` carries the max of a set of indices to the min of
its image and vice versa. -/

theorem min'_image_rev {P : Finset (Fin (n + 1))} (hP : P.Nonempty)
    (h : (P.image Fin.rev).Nonempty) :
    (P.image Fin.rev).min' h = (P.max' hP).rev := by
  refine le_antisymm (min'_le _ _ (mem_image_of_mem _ (max'_mem P hP))) ?_
  refine le_min' _ _ _ ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact Fin.rev_le_rev.mpr (le_max' P x hx)

theorem max'_image_rev {P : Finset (Fin (n + 1))} (hP : P.Nonempty)
    (h : (P.image Fin.rev).Nonempty) :
    (P.image Fin.rev).max' h = (P.min' hP).rev := by
  refine le_antisymm ?_ (le_max' _ _ (mem_image_of_mem _ (min'_mem P hP)))
  refine max'_le _ _ _ ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact Fin.rev_le_rev.mpr (min'_le P x hx)

/-- The index set defining `indeg (D s⃗)` is the `rev`-image of the index
set defining `tp(s⃗)`: `(D s⃗)(j) < C(n,j) ⟺ s(n−j) > 0`. -/
theorem Dvec_indeg_filter (s : Fin (n + 1) → ℕ) :
    (univ.filter fun j : Fin (n + 1) => Dvec s j < n.choose j.val) =
      (univ.filter fun j : Fin (n + 1) => 0 < s j).image Fin.rev := by
  ext j
  rw [mem_filter, mem_image]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    refine ⟨j.rev, ?_, Fin.rev_rev j⟩
    have hd : Dvec s j = n.choose j.val - s j.rev := rfl
    omega
  · rintro ⟨x, hx, rfl⟩
    have hd : Dvec s x.rev = n.choose x.rev.val - s x.rev.rev := rfl
    rw [Fin.rev_rev] at hd
    have hpos : 0 < n.choose x.rev.val := Nat.choose_pos x.rev.is_le
    omega

/-- The index set defining `tp(D s⃗)` is the `rev`-image of the index set
defining `indeg(s⃗)`: `(D s⃗)(j) > 0 ⟺ s(n−j) < C(n,n−j)`. -/
theorem Dvec_top_filter (s : Fin (n + 1) → ℕ) :
    (univ.filter fun j : Fin (n + 1) => 0 < Dvec s j) =
      (univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).image
        Fin.rev := by
  ext j
  rw [mem_filter, mem_image]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    refine ⟨j.rev, ?_, Fin.rev_rev j⟩
    have hd : Dvec s j = n.choose j.val - s j.rev := rfl
    have hsym : n.choose j.rev.val = n.choose j.val := choose_rev_val j
    omega
  · rintro ⟨x, hx, rfl⟩
    have hd : Dvec s x.rev = n.choose x.rev.val - s x.rev.rev := rfl
    rw [Fin.rev_rev] at hd
    have hsym : n.choose x.rev.val = n.choose x.val := choose_rev_val x
    omega

/-- `eq:alexander-stats`, first half: `indeg(D s⃗) = n − tp(s⃗)`.  Holds
for **every** `s⃗`, and the boundary conventions line up exactly: the
void family (`tp = −1`) dualises to the full simplex (`indeg = n+1`). -/
theorem indeg_Dvec (s : Fin (n + 1) → ℕ) :
    (indeg (Dvec s) : ℤ) = n - top s := by
  rw [indeg, top]
  simp only [Dvec_indeg_filter s]
  split_ifs with h1 h2 h2
  · rw [min'_image_rev h2 h1, Fin.val_rev]
    have := Fin.is_le ((univ.filter fun j : Fin (n + 1) => 0 < s j).max' h2)
    omega
  · exact absurd (image_nonempty.mp h1) h2
  · exact absurd (h2.image _) h1
  · omega

/-- `eq:alexander-stats`, second half: `tp(D s⃗) = n − indeg(s⃗)`.  Holds
for **every** `s⃗`; the full simplex (`indeg = n+1`) dualises to the void
family (`tp = −1`). -/
theorem top_Dvec (s : Fin (n + 1) → ℕ) :
    top (Dvec s) = n - (indeg s : ℤ) := by
  rw [top, indeg]
  simp only [Dvec_top_filter s]
  split_ifs with h1 h2 h2
  · rw [max'_image_rev h2 h1, Fin.val_rev]
    have := Fin.is_le
      ((univ.filter fun j : Fin (n + 1) => s j < n.choose j.val).min' h2)
    omega
  · exact absurd (image_nonempty.mp h1) h2
  · exact absurd (h2.image _) h1
  · omega

/-! ## `cor-persymmetry` -/

/-- `cor-persymmetry`: `A[τ][ρ] = A[n−ρ][n−τ]` — for **all** integer
indices, since `D` is a bijection of `𝓕_n` carrying the class `(τ,ρ)`
onto the class `(n−ρ, n−τ)`. -/
theorem Amat_persymmetric (n : ℕ) (τ ρ : ℤ) :
    Amat n τ ρ = Amat n ((n : ℤ) - ρ) ((n : ℤ) - τ) := by
  rw [Amat, Amat]
  refine card_bij' (fun s _ => Dvec s) (fun t _ => Dvec t) ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hsF, htop, hind⟩ := mem_filter.mp hs
    refine mem_filter.mpr ⟨Dvec_mem_Fn hsF, ?_, ?_⟩
    · rw [top_Dvec, hind]
    · rw [indeg_Dvec, htop]
  · intro t ht
    obtain ⟨htF, htop, hind⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨Dvec_mem_Fn htF, ?_, ?_⟩
    · rw [top_Dvec, hind]
      omega
    · rw [indeg_Dvec, htop]
      omega
  · intro s hs
    exact Dvec_Dvec_of_mem_Fn (mem_filter.mp hs).1
  · intro t ht
    exact Dvec_Dvec_of_mem_Fn (mem_filter.mp ht).1

/-! ## `prop-fnn2` -/

instance : DecidablePred (IsComplex (n := n)) := fun D =>
  decidable_of_iff
    (IsOrderIdeal D ∧ (∅ : Finset (Fin n)) ∈ D ∧
      ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ D)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
     fun h => ⟨h.ideal, h.empty_mem, h.singleton_mem⟩⟩

/-- `S_n` as a finite set of ℕ-valued vectors: the `f`-vectors of
simplicial complexes on `[n]` (convention (iii)).  The ℕ-valued
counterpart of `Complexes.lean`'s real-valued `Sset` — see
`Sset_eq_image_SnF`. -/
def SnF (n : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (univ.filter fun D : Finset (Finset (Fin n)) => IsComplex D).image fvecN

theorem mem_SnF {s : Fin (n + 1) → ℕ} :
    s ∈ SnF n ↔ ∃ D, IsComplex D ∧ fvecN D = s := by
  simp [SnF]

theorem SnF_subset_Fn : SnF n ⊆ Fn n := fun s hs => by
  obtain ⟨D, hD, rfl⟩ := mem_SnF.mp hs
  exact mem_Fn.mpr ⟨D, hD.ideal, rfl⟩

/-- Article 1's real-valued `S_n` (`Sset`) is the coordinatewise cast of
the ℕ-valued `SnF`: the two developments count the same objects. -/
theorem Sset_eq_image_SnF (n : ℕ) :
    Sset n = (fun s : Fin (n + 1) → ℕ => fun j => (s j : ℝ)) ''
      (SnF n : Set (Fin (n + 1) → ℕ)) := by
  ext x
  constructor
  · rintro ⟨D, hD, rfl⟩
    exact ⟨fvecN D, mem_SnF.mpr ⟨D, hD, rfl⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨D, hD, rfl⟩ := mem_SnF.mp hs
    exact ⟨D, hD, rfl⟩

/-- Properness characterised inside `𝓕_n`: for `n ≥ 1`, membership in
`S_n` says exactly `s(0) = 1` and `s(1) = n` (the manuscript's
`s⃗ ∈ S_n ⟺ s(0) = 1 ∧ s(1) = n` step in `prop-fnn2`'s proof). -/
theorem mem_SnF_iff (hn : 1 ≤ n) {s : Fin (n + 1) → ℕ} :
    s ∈ SnF n ↔
      s ∈ Fn n ∧ s ⟨0, by omega⟩ = 1 ∧ s ⟨1, by omega⟩ = n := by
  constructor
  · intro hs
    obtain ⟨D, hD, rfl⟩ := mem_SnF.mp hs
    exact ⟨mem_Fn.mpr ⟨D, hD.ideal, rfl⟩,
      fEntry_zero hD.ideal hD.nonempty, fEntry_one hD⟩
  · rintro ⟨hsF, h0, h1⟩
    obtain ⟨D, hD, rfl⟩ := mem_Fn.mp hsF
    have hne : D.Nonempty := nonempty_of_fEntry_zero h0
    have hsing : ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ D := by
      have hsub : D.filter (fun t => #t = 1) ⊆
          univ.image fun i : Fin n => ({i} : Finset (Fin n)) := by
        intro t ht
        obtain ⟨i, rfl⟩ := card_eq_one.mp (mem_filter.mp ht).2
        exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
      have hcard : #(univ.image fun i : Fin n => ({i} : Finset (Fin n))) ≤
          #(D.filter fun t => #t = 1) := by
        rw [card_image_of_injective _ Finset.singleton_injective, card_univ,
          Fintype.card_fin]
        exact le_of_eq h1.symm
      have heq := eq_of_subset_of_card_le hsub hcard
      intro i
      have hmem : ({i} : Finset (Fin n)) ∈ D.filter fun t => #t = 1 := by
        rw [heq]
        exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
      exact (mem_filter.mp hmem).1
    exact mem_SnF.mpr ⟨D, ⟨hD, hD.empty_mem hne, hsing⟩, rfl⟩

/-- Linusson's `F^n(m)` at `p = n`, **by counting**: the number of
`s⃗ ∈ 𝓕_n` with `tp(s⃗) ≤ m` (`def-linusson` at `p = n`, where `f₁ ≤ n`
is automatic).  Defined for all integer `m`; per the plan, the recursion
`thm-linusson` is deliberately not part of the formal development. -/
def Fcount (n : ℕ) (m : ℤ) : ℕ :=
  ((Fn n).filter fun s => top s ≤ m).card

/-- `prop-fnn2`: `|S_n| = F^n(n−2)` for `n ≥ 1`.  Properness — two
conditions at the bottom of `s⃗` — is Alexander-dual to the vanishing of
the top two entries of `D s⃗`. -/
theorem card_SnF_eq_Fcount (hn : 1 ≤ n) :
    (SnF n).card = Fcount n ((n : ℤ) - 2) := by
  rw [Fcount]
  refine card_bij' (fun s _ => Dvec s) (fun t _ => Dvec t) ?_ ?_ ?_ ?_
  · -- proper ⟹ the dual has `tp ≤ n − 2`
    intro s hs
    obtain ⟨hsF, h0, h1⟩ := (mem_SnF_iff hn).mp hs
    refine mem_filter.mpr ⟨Dvec_mem_Fn hsF, ?_⟩
    have h2 : 2 ≤ indeg s := by
      rw [le_indeg_iff (by omega)]
      intro j hj
      rcases (by omega : j.val = 0 ∨ j.val = 1) with h | h
      · have hj0 : j = (⟨0, by omega⟩ : Fin (n + 1)) := Fin.ext h
        rw [hj0, h0]
        simp
      · have hj1 : j = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext h
        rw [hj1, h1, Nat.choose_one_right]
    rw [top_Dvec]
    omega
  · -- `tp ≤ n − 2` ⟹ the dual is proper
    intro t ht
    obtain ⟨htF, htop⟩ := mem_filter.mp ht
    rw [mem_SnF_iff hn]
    refine ⟨Dvec_mem_Fn htF, ?_, ?_⟩
    · -- `(D t⃗)(0) = C(n,0) − t(n) = 1`
      have hrev : ((⟨0, by omega⟩ : Fin (n + 1)).rev).val = n := by
        show n + 1 - (0 + 1) = n
        omega
      have hz : t ((⟨0, by omega⟩ : Fin (n + 1)).rev) = 0 :=
        apply_eq_zero_of_top_lt (lt_of_le_of_lt htop (by rw [hrev]; omega))
      show n.choose (⟨0, by omega⟩ : Fin (n + 1)).val -
        t ((⟨0, by omega⟩ : Fin (n + 1)).rev) = 1
      rw [hz]
      show n.choose 0 - 0 = 1
      simp
    · -- `(D t⃗)(1) = C(n,1) − t(n−1) = n`
      have hrev : ((⟨1, by omega⟩ : Fin (n + 1)).rev).val = n - 1 := by
        show n + 1 - (1 + 1) = n - 1
        omega
      have hz : t ((⟨1, by omega⟩ : Fin (n + 1)).rev) = 0 :=
        apply_eq_zero_of_top_lt (lt_of_le_of_lt htop (by rw [hrev]; omega))
      show n.choose (⟨1, by omega⟩ : Fin (n + 1)).val -
        t ((⟨1, by omega⟩ : Fin (n + 1)).rev) = n
      rw [hz]
      show n.choose 1 - 0 = n
      simp [Nat.choose_one_right]
  · intro s hs
    exact Dvec_Dvec_of_mem_Fn (SnF_subset_Fn hs)
  · intro t ht
    exact Dvec_Dvec_of_mem_Fn (mem_filter.mp ht).1

end ExteriorConvex
