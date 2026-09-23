/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 1 of the §§4–6 formalisation: order ideals, complexes and `f`-vectors

Formalisation of `def-complex` and `def-proper` from
`article/exterior-convex_article1_latest.org`, together with the supporting
facts the later rungs (local LYM, Kozlov's theorem, the sumset identity)
consume, per `working-notes/PLAN-formalise-rungs-1-4.org`.

Conventions, fixed by the plan:

* Everything here lives in the **degree-0-inclusive space** `Fin (n + 1) → ℝ`:
  the `f`-vector of a complex on `[n]` has entry `j` equal to `f_j`, so entry
  `0` is `f₀`.  This is the manuscript's `x₀,…,x_n`, the space `thm-main` is
  stated in.  It is *not* the existing development's dropped space
  `Fin N → ℝ` (`Kozlov.lean`, `Count.lean`, coordinates 1-indexed via
  `c.val + 1`); the bridge between the two spaces is the translation term of
  the manuscript's `eq:koz-as-ra` and is deliberately **not formalised here**
  — see the comment at `projIncl` below for where it would go.
* `fEntry` is valued in `ℕ` and cast to `ℝ` once, in `fvec`.
* Mathlib has no abstract simplicial complex (its `SimplicialComplex` is the
  geometric one), which is why `IsOrderIdeal`/`IsComplex` are defined here.
-/
import Mathlib

open Finset

namespace ExteriorConvex

variable {n : ℕ}

/-- `def-complex`: an order ideal of the subset lattice `𝒫([n])` — a family
of subsets of `Fin n` closed under taking subsets.  The manuscript's `𝒟 n`.
Following the manuscript's convention of 2026-09-13 exactly, the **empty
family qualifies** (the condition holds vacuously), and so do order ideals
omitting some singleton. -/
def IsOrderIdeal (D : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃s t : Finset (Fin n)⦄, s ∈ D → t ⊆ s → t ∈ D

/-- `def-complex`: a simplicial complex on `[n]` in the strict sense — the
manuscript's convention (iii), Kozlov's convention: an order ideal containing
`∅` and every singleton.  The manuscript's `𝒮 n`. -/
structure IsComplex (D : Finset (Finset (Fin n))) : Prop where
  ideal : IsOrderIdeal D
  empty_mem : (∅ : Finset (Fin n)) ∈ D
  singleton_mem : ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ D

/-- A complex is in particular a non-empty family. -/
theorem IsComplex.nonempty {D : Finset (Finset (Fin n))} (hD : IsComplex D) :
    D.Nonempty :=
  ⟨∅, hD.empty_mem⟩

/-- `eq:complex`: `f_j(Δ)`, the number of faces of cardinality `j` (the
manuscript's cardinality convention, matching Kozlov).  Valued in `ℕ`;
cast once, in `fvec`. -/
def fEntry (D : Finset (Finset (Fin n))) (j : ℕ) : ℕ :=
  #(D.filter fun s => #s = j)

/-- The `f`-vector of an order ideal as a point of the degree-0-inclusive
space `Fin (n+1) → ℝ`. -/
def fvec (D : Finset (Finset (Fin n))) : Fin (n + 1) → ℝ :=
  fun j => (fEntry D j.val : ℝ)

/-- `def-proper` / `eq:proper`: `S_n`, the set of `f`-vectors of simplicial
complexes on `[n]` (equivalently, by `prop-dictionary` and `def-proper`, the
set of proper Hilbert functions).  Every element begins `(1, n, …)`. -/
def Sset (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | ∃ D, IsComplex D ∧ fvec D = x}

/-! ## Supporting fact 1: the degree-0 entry, and the empty-ideal split

The manuscript (after `def-complex`, and `prop-dictionary`(3)) makes the
split explicit: `f₀(Δ) = 1` for every non-empty order ideal, and
`f₀(∅) = 0`. -/

/-- Every `fEntry` of the empty order ideal vanishes; in particular
`f₀(∅) = 0`, the manuscript's empty-ideal case. -/
@[simp] theorem fEntry_empty (j : ℕ) :
    fEntry (∅ : Finset (Finset (Fin n))) j = 0 := by
  simp [fEntry]

/-- A non-empty order ideal contains the empty face. -/
theorem IsOrderIdeal.empty_mem {D : Finset (Finset (Fin n))}
    (hD : IsOrderIdeal D) (hne : D.Nonempty) : (∅ : Finset (Fin n)) ∈ D := by
  obtain ⟨s, hs⟩ := hne
  exact hD hs (empty_subset s)

/-- `f₀(Δ) = 1` for every non-empty order ideal `Δ`. -/
theorem fEntry_zero {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D)
    (hne : D.Nonempty) : fEntry D 0 = 1 := by
  have hfilter : D.filter (fun s => #s = 0) = {∅} := by
    ext s
    simp only [mem_filter, card_eq_zero, mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hD.empty_mem hne, h⟩⟩
  rw [fEntry, hfilter, card_singleton]

/-- Conversely, an order ideal with `f₀ = 1` is non-empty. -/
theorem nonempty_of_fEntry_zero {D : Finset (Finset (Fin n))}
    (h : fEntry D 0 = 1) : D.Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  subst hne
  simp at h

/-! ## Supporting fact 2: properness -/

/-- Properness (`def-proper`): a complex on `[n]` has `f₁ = n`, since it
contains every singleton and nothing else has cardinality one. -/
theorem fEntry_one {D : Finset (Finset (Fin n))} (hD : IsComplex D) :
    fEntry D 1 = n := by
  have hfilter : D.filter (fun s => #s = 1) =
      Finset.univ.image (fun i : Fin n => ({i} : Finset (Fin n))) := by
    ext s
    simp only [mem_filter, card_eq_one, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨-, a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨hD.singleton_mem a, a, rfl⟩
  rw [fEntry, hfilter, card_image_of_injective _ Finset.singleton_injective,
    card_univ, Fintype.card_fin]

/-! ## Supporting fact 3: the trivial bounds -/

/-- `f_j = 0` beyond the ambient dimension: a subset of `[n]` has at most `n`
elements.  (No complex hypothesis is needed.) -/
theorem fEntry_eq_zero_of_lt {D : Finset (Finset (Fin n))} {j : ℕ}
    (hj : n < j) : fEntry D j = 0 := by
  rw [fEntry, card_eq_zero, filter_eq_empty_iff]
  intro s _
  have hcard : #s ≤ n := by
    simpa using card_le_card (subset_univ s)
  omega

/-- `f_j(Δ) ≤ C(n, j)` always: there are only `C(n, j)` subsets of `[n]` of
cardinality `j`. -/
theorem fEntry_le_choose (D : Finset (Finset (Fin n))) (j : ℕ) :
    fEntry D j ≤ n.choose j := by
  have hsub : D.filter (fun s => #s = j) ⊆ Finset.univ.powersetCard j := by
    intro s hs
    rw [mem_powersetCard]
    exact ⟨subset_univ s, (mem_filter.mp hs).2⟩
  calc fEntry D j ≤ #(Finset.univ.powersetCard j) := card_le_card hsub
    _ = n.choose j := by rw [card_powersetCard, card_univ, Fintype.card_fin]

/-! ## Supporting fact 4: `S_n` is finite and non-empty

Finiteness is load-bearing, not hygiene: it makes every convex hull below a
hull of a finite set, which is the only case `Bridge.lean` handles. -/

/-- `S_n` is a finite set: it is the image of the finite type
`Finset (Finset (Fin n))` under `fvec`. -/
theorem Sset_finite (n : ℕ) : (Sset n).Finite := by
  have himage : Sset n = fvec '' {D : Finset (Finset (Fin n)) | IsComplex D} :=
    rfl
  rw [himage]
  exact (Set.toFinite _).image _

/-- `S_n` is non-empty for every `n`: the full power set of `[n]` is a
complex (for `n = 0` it is `{∅}`, the complex with the empty face only). -/
theorem Sset_nonempty (n : ℕ) : (Sset n).Nonempty := by
  refine ⟨fvec (Finset.univ : Finset (Finset (Fin n))), Finset.univ, ?_, rfl⟩
  exact ⟨fun s t _ _ => mem_univ t, mem_univ _, fun i => mem_univ _⟩

/-! ## Supporting fact 5: the shift and the projection

`def-shift`: `shift^d : ℝ^{n+1} → ℝ^{N+1}` prepends `d` zeros to the whole
vector — degree-0 entry included — and pads with zeros on the right.  It is
the coordinate inclusion `e_j ↦ e_{j+d}`, and its *linearity* (rather than
affinity) is what makes `thm-main` come out with no leftover translation
vector, so it is packaged as a `LinearMap` (`LinearMap.image_convexHull`
needs exactly that). -/

/-- `def-shift`, degree-0-inclusively: the linear map
`(Fin (n+1) → ℝ) →ₗ[ℝ] (Fin (N+1) → ℝ)` with entry `j` of the image equal to
entry `j - d` of the argument when `d ≤ j ≤ d + n`, and `0` otherwise. -/
def shiftIncl (N d : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) where
  toFun x := fun j =>
    if h : d ≤ j.val ∧ j.val - d ≤ n then x ⟨j.val - d, Nat.lt_succ_of_le h.2⟩
    else 0
  map_add' x y := by
    funext j
    by_cases h : d ≤ j.val ∧ j.val - d ≤ n
    · simp only [Pi.add_apply, dite_eq_left h]
    · simp only [Pi.add_apply, dite_eq_right h, add_zero]
  map_smul' c x := by
    funext j
    by_cases h : d ≤ j.val ∧ j.val - d ≤ n
    · simp only [Pi.smul_apply, dite_eq_left h, RingHom.id_apply, smul_eq_mul]
    · simp only [Pi.smul_apply, dite_eq_right h, RingHom.id_apply, smul_eq_mul,
        mul_zero]

@[simp] theorem shiftIncl_apply (N d : ℕ) (x : Fin (n + 1) → ℝ)
    (j : Fin (N + 1)) :
    shiftIncl N d x j =
      if h : d ≤ j.val ∧ j.val - d ≤ n then x ⟨j.val - d, Nat.lt_succ_of_le h.2⟩
      else 0 := rfl

/-- The projection `π` of the manuscript's §"Notation", forgetting the
degree-0 entry: `(x₀, x₁, …, x_n) ↦ (x₁, …, x_n)`, as a linear map.

**The seam with the existing development is here and is deliberately left
open**: the existing files (`Kozlov.lean`, `Count.lean`) live in the dropped
space `Fin N → ℝ` with coordinates 1-indexed via `c.val + 1`, and identifying
`projIncl '' (convexHull ℝ (Sset n))` with their `rasimp`/Kozlov-simplex
objects is exactly the translation term of the manuscript's `eq:koz-as-ra`.
That reconciliation is out of scope per the plan
(`working-notes/PLAN-formalise-rungs-1-4.org`, Conventions), and would go
here if ever undertaken. -/
def projIncl : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x := fun j => x j.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem projIncl_apply (x : Fin (n + 1) → ℝ) (j : Fin n) :
    projIncl x j = x j.succ := rfl

end ExteriorConvex
