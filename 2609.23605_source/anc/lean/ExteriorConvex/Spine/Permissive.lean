/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung 5 of the §§4–6 formalisation: properness, and the permissive convention

Formalisation of §5.1 ("Properness, and the permissive convention") of
`article/exterior-convex_article1_latest.org`: `eq:Splus`, `lem-mu-permissive`,
`prop-permissive-hull`, `prop-properness-facet` (in part — see below) and
`prop-permissive-fibres`, continuing `working-notes/PLAN-formalise-rungs-1-4.org`'s
conventions in the degree-0-inclusive space `Fin (n+1) → ℝ`.

* `SsetPerm` is `eq:Splus`: `S_n⁺`, the `f`-vectors of the *non-empty* order
  ideals — convention (ii) in place of (iii).
* `e0` is the manuscript's `e₀`, the `f`-vector of `{∅}` — a standard basis
  vector, **not** the origin (the manuscript flags exactly this drafting trap).
* `lymChainPerm` / `hull_skel_perm_eq` are `lem-mu-permissive`, inclusively:
  `μ₁ = 1` relaxed to `μ₁ ≤ 1`, the hull gaining the vertex `e₀` with weight
  `λ₀ = 1 − μ₁`.  The proof is `lem-mu`'s barycentric computation with the sum
  extended to start at `j = 0` — literally: `skel n 0 = e₀` (`skel_zero`), so
  the generator family is `skel n '' Icc 0 n` and `LYM.lean`'s telescoping
  machinery (`muOf`, `sum_mu_telescope`) applies verbatim from `k = 0`, where
  `μ₀ = x₀/C(n,0) = 1`.
* `permissive_hull` / `hull_SsetPerm_eq` are `prop-permissive-hull`; the `⊆`
  inclusion uses that `lym` (`LYM.lean`) was stated for **order ideals**, not
  complexes — the manuscript's parenthetical "which assumes only that Δ is an
  order ideal" is true of the Lean development as well, so local LYM needs no
  reproving here.
* `rasimpB` and the `properness_*` theorems are `prop-properness-facet` **minus
  the facet-dimension clause**: formalised are the identity `eq:permissive-simplex`
  (`rasimpB_eq_insert_hull`), the validity of `x₁ ≤ n` (`properness_valid`), and
  that its tight face is exactly `Koz(n) = conv(S_n)` (`properness_tight_face`).
  The claim that this face *is a facet* (codimension one) rests on the
  affine-independence clauses of `lem-mu`/`lem-mu-permissive`, which rungs 2 and
  5 both deliberately skip — the same precedent as rung 3 leaving `cor-facets`'
  "exactly the facets" clause unformalised.  Note also that the manuscript's
  `∠(b̄)` (`def-rasimp`, §8, 1-indexed legs, dropped space) is **not defined in
  Lean**; `rasimpB n` is its 0-indexed inclusive-space reading, exactly the
  reading `prop-properness-facet` itself fixes ("read with legs and coordinates
  indexed 0,1,…,n"), and under that reading its vertex list is
  `skel n '' Icc 0 n` by definition.  The identification with §8's dropped-space
  `rasimp` machinery is part of the `eq:koz-as-ra` seam left open at `projIncl`.
* `permissive_fibres` / `fibre_eq` / `fibres_disjoint` are
  `prop-permissive-fibres`, the file's main prize: until 2026-09-13 the
  manuscript stated it without proof.  The genuinely new ingredient is
  `relabel` / `fEntry_relabel` / `exists_relabel`: `f`-vectors are invariant
  under relabelling the ground set along an injection `Fin k ↪ Fin n`.  The
  `k = 0` degeneration the manuscript checks explicitly is `Sset_zero` /
  `fibre_zero`; in the main proofs no case split is needed — the machinery
  degenerates correctly on its own, as the manuscript says it does.

**Not formalised, deliberately**: the affine-independence / dimension clauses
(as above); and the `n = 4` census (168 order ideals, 25 `f`-vectors, block
sizes 1,1,2,5,16), which stays a Sage verification in the manuscript's flowing
text.  The census is finite and decidable-looking, but kernel `decide` cannot
survive `2^16` families and `native_decide` would add the axiom
`Lean.ofReduceBool`, breaking the three-standard-axioms property the
development asserts in print.  **Do not add `native_decide` here.**
-/
import Mathlib
import ExteriorConvex.Spine.Complexes
import ExteriorConvex.Spine.LYM
import ExteriorConvex.Spine.KozlovThm

open Finset

namespace ExteriorConvex

variable {n : ℕ}

/-! ## `e₀` and `S_n⁺` (`eq:Splus`) -/

/-- The manuscript's `e₀` in the inclusive space: the `f`-vector of the order
ideal `{∅}` — the point properness removes.  A standard basis vector, not the
origin (it is `proj e₀` that is `0 ∈ ℝ^n`). -/
def e0 (n : ℕ) : Fin (n + 1) → ℝ := fun i => if i.val = 0 then 1 else 0

/-- The `0`-skeleton point is `e₀`: `skel n 0 = e₀`.  This is what lets the
permissive generator family be written as `skel n '' Icc 0 n`. -/
theorem skel_zero (n : ℕ) : skel n 0 = e0 n := by
  funext i
  simp only [skel, e0]
  split_ifs with h1 h2
  · rfl
  · exact absurd (Nat.le_zero.mp h2) h1
  · rfl

/-- `eq:Splus`: `S_n⁺`, the set of `f`-vectors of the *non-empty* order ideals
on `[n]` — convention (ii): every singleton no longer required, `Δ ≠ ∅` kept. -/
def SsetPerm (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | ∃ D, IsOrderIdeal D ∧ D.Nonempty ∧ fvec D = x}

/-- `S_n ⊆ S_n⁺`: every complex is a non-empty order ideal. -/
theorem Sset_subset_SsetPerm (n : ℕ) : Sset n ⊆ SsetPerm n := by
  rintro _ ⟨D, hD, rfl⟩
  exact ⟨D, hD.ideal, hD.nonempty, rfl⟩

/-- `S_n⁺` is a finite set, like `S_n` (image of a finite type under `fvec`). -/
theorem SsetPerm_finite (n : ℕ) : (SsetPerm n).Finite := by
  apply Set.Finite.subset ((Set.toFinite
    (Set.univ : Set (Finset (Finset (Fin n))))).image fvec)
  rintro _ ⟨D, -, -, rfl⟩
  exact ⟨D, trivial, rfl⟩

/-- `{∅}` is an order ideal. -/
theorem isOrderIdeal_singleton_empty :
    IsOrderIdeal ({∅} : Finset (Finset (Fin n))) := by
  intro s t hs hts
  rw [Finset.mem_singleton] at hs ⊢
  subst hs
  exact Finset.subset_empty.mp hts

/-- The `f`-vector of `{∅}` is `e₀`: one face of cardinality `0`, nothing
else — the manuscript's "as an `f`-vector it is the one of `{∅}`". -/
theorem fvec_singleton_empty : fvec ({∅} : Finset (Finset (Fin n))) = e0 n := by
  funext j
  show (fEntry ({∅} : Finset (Finset (Fin n))) j.val : ℝ) = e0 n j
  rw [fEntry, Finset.filter_singleton]
  simp only [e0]
  rcases Nat.eq_zero_or_pos j.val with h | h
  · rw [ite_eq_left (show #(∅ : Finset (Fin n)) = j.val by
        rw [Finset.card_empty]; omega),
      ite_eq_left h, Finset.card_singleton, Nat.cast_one]
  · rw [ite_eq_right (show ¬#(∅ : Finset (Fin n)) = j.val by
        rw [Finset.card_empty]; omega),
      ite_eq_right (by omega : ¬(j.val = 0)), Finset.card_empty,
      Nat.cast_zero]

/-- `e₀ ∈ S_n⁺`, witnessed by `{∅}`. -/
theorem e0_mem_SsetPerm (n : ℕ) : e0 n ∈ SsetPerm n :=
  ⟨{∅}, isOrderIdeal_singleton_empty, ⟨∅, Finset.mem_singleton_self ∅⟩,
    fvec_singleton_empty⟩

/-! ## `lem-mu-permissive`: the permissive LYM chain

The chain set with `μ₁ = 1` relaxed to `μ₁ ≤ 1`; the hull description gains
the vertex `e₀`, whose weight is the slack `λ₀ = 1 − μ₁`.  The
affine-independence clause ("an `n`-simplex, one dimension more") is **not
formalised** — see the file header. -/

/-- The right-hand side of `eq:mu-permissive`, in inclusive coordinates:
`x₀ = 1`, `μ₁ ≤ 1` (i.e. `x₁ ≤ n`), the LYM chain `μ_j ≥ μ_{j+1}` for
`1 ≤ j ≤ n-1`, and `μ_n ≥ 0`. -/
def lymChainPerm (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = 1 ∧ x 1 ≤ (n : ℝ) ∧
    (∀ j, (hj : 1 ≤ j) → (hjn : j ≤ n - 1) →
      x ⟨j + 1, by omega⟩ / (n.choose (j + 1) : ℝ) ≤
        x ⟨j, by omega⟩ / (n.choose j : ℝ)) ∧
    0 ≤ x (Fin.last n)}

/-- The strict chain set is contained in the permissive one (`μ₁ = 1` implies
`μ₁ ≤ 1`). -/
theorem lymChain_subset_lymChainPerm (n : ℕ) :
    lymChain n ⊆ lymChainPerm n := by
  rintro x ⟨h0, h1, hc, hlast⟩
  exact ⟨h0, le_of_eq h1, hc, hlast⟩

/-- The permissive chain set is convex: an intersection of one hyperplane and
finitely many half-spaces, checked directly (cf. `convex_lymChain`). -/
theorem convex_lymChainPerm (n : ℕ) : Convex ℝ (lymChainPerm n) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx0, hy0, mul_one]
    exact hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : a * x 1 ≤ a * (n : ℝ) := mul_le_mul_of_nonneg_left hx1 ha
    have h2 : b * y 1 ≤ b * (n : ℝ) := mul_le_mul_of_nonneg_left hy1 hb
    have h3 : a * (n : ℝ) + b * (n : ℝ) = (n : ℝ) := by
      rw [← add_mul, hab, one_mul]
    linarith
  · intro j hj hjn
    have h1 := hxc j hj hjn
    have h2 := hyc j hj hjn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div,
      mul_div_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha)
      (mul_le_mul_of_nonneg_left h2 hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hxn) (mul_nonneg hb hyn)

/-- `e₀` satisfies the permissive chain description (all its LYM ratios past
`μ₀` vanish, and `μ₁ = 0 ≤ 1`). -/
theorem e0_mem_lymChainPerm (hn : 1 ≤ n) : e0 n ∈ lymChainPerm n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [e0]
  · rw [fin_one_eq hn]
    simp only [e0]
    rw [ite_eq_right (by omega : ¬(1 = 0))]
    exact Nat.cast_nonneg n
  · intro j hj hjn
    simp only [e0]
    rw [ite_eq_right (by omega : ¬(j + 1 = 0)),
      ite_eq_right (by omega : ¬(j = 0)), zero_div, zero_div]
  · simp only [e0, Fin.val_last]
    split_ifs with h
    · exact zero_le_one
    · exact le_refl 0

/-- The permissive generators satisfy the permissive chain:
`{e₀} ∪ skelSet n ⊆` the RHS of `eq:mu-permissive`. -/
theorem e0_skelSet_subset_lymChainPerm (hn : 1 ≤ n) :
    {e0 n} ∪ skelSet n ⊆ lymChainPerm n := by
  rw [Set.union_subset_iff, Set.singleton_subset_iff]
  exact ⟨e0_mem_lymChainPerm hn,
    (skelSet_subset_lymChain hn).trans (lymChain_subset_lymChainPerm n)⟩

/-- The hard half of `lem-mu-permissive`: a point of the permissive chain set
is a convex combination of `e₀` and the skeleta, with barycentric coordinates
`λ_j = μ_j − μ_{j+1}` (`1 ≤ j < n`), `λ_n = μ_n`, and `λ₀ = 1 − μ₁` on the new
vertex — the slack in `μ₁ ≤ 1`.  Since `skel n 0 = e₀` and
`μ₀ = x₀/C(n,0) = 1`, this is `lymChain_subset_hull`'s telescoping sum started
at `j = 0` instead of `j = 1`: uniformly `λ_j = μ_j − μ_{j+1}` on `0 ≤ j ≤ n`. -/
theorem lymChainPerm_subset_hull (hn : 1 ≤ n) :
    lymChainPerm n ⊆ convexHull ℝ ({e0 n} ∪ skelSet n) := by
  intro x hx
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  set w : ℕ → ℝ := fun j => muOf n x j - muOf n x (j + 1) with hw
  -- μ₀ = 1, from x₀ = 1 and C(n,0) = 1.
  have hmu0 : muOf n x 0 = 1 := by
    rw [muOf_of_le (Nat.zero_le n), Nat.choose_zero_right, Nat.cast_one,
      div_one, show (⟨0, Nat.lt_succ_of_le (Nat.zero_le n)⟩ : Fin (n + 1)) = 0
        from Fin.ext rfl, hx0]
  -- μ₁ ≤ 1, from x₁ ≤ n.
  have hmu1 : muOf n x 1 ≤ 1 := by
    rw [muOf_of_le hn, ← fin_one_eq hn, Nat.choose_one_right,
      div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (by omega))]
    exact hx1
  -- The weights are non-negative; the new case is `j = 0`, where
  -- `w 0 = 1 − μ₁` is the slack in properness.
  have hw0 : ∀ j ∈ Finset.Icc 0 n, 0 ≤ w j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hw]
      simp only []
      rw [hmu0]
      linarith [hmu1]
    · rcases eq_or_lt_of_le hj.2 with hjn | hjn
      · subst hjn
        rw [hw]
        simp only []
        rw [muOf_of_gt (Nat.lt_succ_self j), sub_zero, muOf_of_le (le_refl j),
          Nat.choose_self, Nat.cast_one, div_one]
        exact hxn
      · have h := hxc j hj1 (by omega)
        rw [hw]
        simp only []
        rw [muOf_of_le (by omega : j ≤ n), muOf_of_le (by omega : j + 1 ≤ n),
          sub_nonneg]
        exact h
  -- The weights sum to 1 = μ₀ (telescoping from 0).
  have hsum : ∑ j ∈ Finset.Icc 0 n, w j = 1 := by
    rw [hw, sum_mu_telescope x (Nat.zero_le n), hmu0]
  -- Each generator is in the generating set (`j = 0` gives `e₀`).
  have hz : ∀ j ∈ Finset.Icc 0 n, skel n j ∈ {e0 n} ∪ skelSet n := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · exact Set.mem_union_left _ (by rw [Set.mem_singleton_iff, skel_zero])
    · exact Set.mem_union_right _ ⟨j, Set.mem_Icc.mpr ⟨hj1, hj.2⟩, rfl⟩
  -- The convex combination reconstructs `x`.
  have hrepr : ∑ j ∈ Finset.Icc 0 n, w j • skel n j = x := by
    funext i
    rw [Finset.sum_apply]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · have hval : ∀ j ∈ Finset.Icc 0 n, (w j • skel n j) i = w j := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul,
          show skel n j i = 1 by simp [skel, hi0], mul_one]
      rw [Finset.sum_congr rfl hval, hsum]
      have hi : i = 0 := Fin.ext hi0
      rw [hi, hx0]
    · have hkn : i.val ≤ n := by omega
      have hval : ∀ j ∈ Finset.Icc 0 n, (w j • skel n j) i =
          if i.val ≤ j then w j * (n.choose i.val : ℝ) else 0 := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul]
        by_cases hkj : i.val ≤ j
        · rw [ite_eq_left hkj, show skel n j i = (n.choose i.val : ℝ) by
            simp only [skel]; rw [ite_eq_right (by omega), ite_eq_left hkj]]
        · rw [ite_eq_right hkj, show skel n j i = 0 by
            simp only [skel]; rw [ite_eq_right (by omega), ite_eq_right hkj],
            mul_zero]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
      have hfilter : (Finset.Icc 0 n).filter (fun j => i.val ≤ j) =
          Finset.Icc i.val n := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilter, ← Finset.sum_mul, sum_mu_telescope x hkn,
        muOf_of_le hkn,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne')]
  have hcm := Finset.centerMass_mem_convexHull (Finset.Icc 0 n) hw0
    (by rw [hsum]; exact zero_lt_one) hz
  rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hrepr] at hcm

/-- `lem-mu-permissive` (the permissive LYM chain): the convex hull of `e₀`
and the skeleta is exactly the permissive chain set.  The
affine-independence clause ("an `n`-simplex") is not formalised — see the
file header. -/
theorem hull_skel_perm_eq (hn : 1 ≤ n) :
    convexHull ℝ ({e0 n} ∪ skelSet n) = lymChainPerm n :=
  Set.Subset.antisymm
    (convexHull_min (e0_skelSet_subset_lymChainPerm hn) (convex_lymChainPerm n))
    (lymChainPerm_subset_hull hn)

/-! ## `prop-permissive-hull`: Kozlov's theorem, permissive form -/

/-- The `⊆` computation in `prop-permissive-hull`'s proof: the `f`-vector of a
non-empty order ideal satisfies the permissive chain — `x₀ = 1` (downward
closure and non-emptiness force `∅ ∈ Δ`), `x₁ ≤ n` (only `n` singletons
exist), the LYM chain (`lym`, **which assumes only an order ideal, not a
complex** — the manuscript's parenthetical, true of the Lean statement too),
and `x_n ≥ 0` (a cardinality). -/
theorem SsetPerm_subset_lymChainPerm (hn : 1 ≤ n) :
    SsetPerm n ⊆ lymChainPerm n := by
  rintro _ ⟨D, hD, hne, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (fEntry D (0 : Fin (n + 1)).val : ℝ) = 1
    rw [Fin.val_zero, fEntry_zero hD hne, Nat.cast_one]
  · rw [fin_one_eq hn]
    show (fEntry D 1 : ℝ) ≤ (n : ℝ)
    have h := fEntry_le_choose D 1
    rw [Nat.choose_one_right] at h
    exact_mod_cast h
  · intro j hj hjn
    exact lym hD hj hjn
  · exact Nat.cast_nonneg _

/-- The `⊇` direction's generators: all `n + 1` vertices are attained — `e₀`
by `{∅}` and each skeleton point by the complete `j`-skeleton. -/
theorem e0_skelSet_subset_SsetPerm (n : ℕ) :
    {e0 n} ∪ skelSet n ⊆ SsetPerm n := by
  rw [Set.union_subset_iff, Set.singleton_subset_iff]
  exact ⟨e0_mem_SsetPerm n, skelSet_subset_Sset.trans (Sset_subset_SsetPerm n)⟩

/-- `prop-permissive-hull`, H-description form: `conv(S_n⁺)` is exactly the
permissive chain set. -/
theorem hull_SsetPerm_eq (hn : 1 ≤ n) :
    convexHull ℝ (SsetPerm n) = lymChainPerm n := by
  apply Set.Subset.antisymm
  · exact convexHull_min (SsetPerm_subset_lymChainPerm hn) (convex_lymChainPerm n)
  · rw [← hull_skel_perm_eq hn]
    exact convexHull_mono (e0_skelSet_subset_SsetPerm n)

/-- `prop-permissive-hull` (Kozlov's theorem, permissive form): for `n ≥ 1`,
`conv(S_n⁺) = conv({e₀} ∪ {F̃_1, …, F̃_n})` — the hull acquires exactly one
more vertex, `e₀`.  (The manuscript states this projected; this is the
inclusive form, cf. `kozlov`.) -/
theorem permissive_hull (hn : 1 ≤ n) :
    convexHull ℝ (SsetPerm n) = convexHull ℝ ({e0 n} ∪ skelSet n) := by
  rw [hull_SsetPerm_eq hn, hull_skel_perm_eq hn]

/-! ## `prop-properness-facet`: properness is a facet (minus the dimension
clause — see the file header for exactly what is and is not carried) -/

/-- `∠(b̄)` for `b̄ = (C(n,0), …, C(n,n))`, in `prop-properness-facet`'s own
0-indexed inclusive reading of `def-rasimp`: the convex hull of the `n + 1`
points `v_j = (b_0, …, b_j, 0, …, 0)`, `j = 0, …, n` — which are exactly
`skel n j` (for `j = 0`: `e₀`, by `skel_zero`).  The manuscript's `∠` itself
(§8, 1-indexed legs, dropped space) is not defined in this development; see
the file header. -/
def rasimpB (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  convexHull ℝ (skel n '' Set.Icc 0 n)

/-- `eq:permissive-verts`: the vertex list of `∠(b̄)` is `e₀` together with
the skeleton points. -/
theorem skel_image_Icc (n : ℕ) :
    skel n '' Set.Icc 0 n = {e0 n} ∪ skelSet n := by
  have hsplit : Set.Icc 0 n = {0} ∪ Set.Icc 1 n := by
    ext j
    simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff]
    omega
  rw [hsplit, Set.image_union, Set.image_singleton, skel_zero]
  rfl

/-- `eq:permissive-simplex` (`prop-properness-facet`'s identity):
`∠(b̄) = conv({e₀} ∪ Koz(n))`, with `Koz(n) = conv(S_n)` per
`def-kozsimplex`. -/
theorem rasimpB_eq_insert_hull (hn : 1 ≤ n) :
    rasimpB n = convexHull ℝ ({e0 n} ∪ convexHull ℝ (Sset n)) := by
  rw [rasimpB, skel_image_Icc, convexHull_convexHull_union_right,
    ← convexHull_convexHull_union_right ({e0 n}) (skelSet n), ← kozlov hn,
    convexHull_convexHull_union_right]

/-- `∠(b̄)` is the permissive chain set (so `eq:permissive-hull-incl`:
`conv(S_n⁺) = ∠(b̄)`, see `hull_SsetPerm_eq_rasimpB`). -/
theorem rasimpB_eq_lymChainPerm (hn : 1 ≤ n) :
    rasimpB n = lymChainPerm n := by
  rw [rasimpB, skel_image_Icc, hull_skel_perm_eq hn]

/-- `eq:permissive-hull-incl` (`prop-permissive-hull`, unprojected form):
`conv(S_n⁺) = ∠(b̄)`. -/
theorem hull_SsetPerm_eq_rasimpB (hn : 1 ≤ n) :
    convexHull ℝ (SsetPerm n) = rasimpB n := by
  rw [hull_SsetPerm_eq hn, rasimpB_eq_lymChainPerm hn]

/-- `prop-properness-facet`, validity half: `x₁ ≤ n` is a valid inequality on
`∠(b̄)` — properness holds everywhere on the permissive hull, as an
inequality. -/
theorem properness_valid (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ rasimpB n) : x 1 ≤ (n : ℝ) := by
  rw [rasimpB_eq_lymChainPerm hn] at hx
  exact hx.2.1

/-- `prop-properness-facet`, tightness half: the face of `∠(b̄)` where
properness is tight — `x₁ = n` — is exactly the Kozlov simplex
`Koz(n) = conv(S_n)`.  (That this face is a *facet*, i.e. of codimension one,
is the unformalised dimension clause — see the file header.) -/
theorem properness_tight_face (hn : 1 ≤ n) :
    {x ∈ rasimpB n | x 1 = (n : ℝ)} = convexHull ℝ (Sset n) := by
  rw [hull_Sset_eq hn]
  ext x
  constructor
  · rintro ⟨hx, h1⟩
    rw [rasimpB_eq_lymChainPerm hn] at hx
    obtain ⟨h0, -, hc, hlast⟩ := hx
    exact ⟨h0, h1, hc, hlast⟩
  · rintro ⟨h0, h1, hc, hlast⟩
    refine ⟨?_, h1⟩
    rw [rasimpB_eq_lymChainPerm hn]
    exact ⟨h0, le_of_eq h1, hc, hlast⟩

/-! ## `prop-permissive-fibres`: the permissive set is fibred by `f₁`

The new ingredient is relabelling invariance: `f`-vectors are unchanged under
transporting a family of faces along an injection `Fin k ↪ Fin n`
(`Finset.map`), because `Finset.card_map` preserves every cardinality.  This
is the lemma the development did not have and the manuscript's proof uses
twice (once through a bijection `V → [k]`, once through an arbitrary
injection `[k] ↪ [n]`). -/

variable {k : ℕ}

/-- `ι_k` of `prop-permissive-fibres`: append `n − k` zeros,
`ℝ^{k+1} → ℝ^{n+1}`.  It is `shift⁰` with a larger target, hence linear. -/
def iotaIncl (n k : ℕ) : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  shiftIncl (n := k) n 0

@[simp] theorem iotaIncl_apply (n k : ℕ) (x : Fin (k + 1) → ℝ)
    (j : Fin (n + 1)) :
    iotaIncl n k x j =
      if h : j.val ≤ k then x ⟨j.val, Nat.lt_succ_of_le h⟩ else 0 := by
  show shiftIncl n 0 x j = _
  rw [shiftIncl_apply]
  by_cases h : j.val ≤ k
  · rw [dite_eq_left (⟨Nat.zero_le _, by omega⟩ : 0 ≤ j.val ∧ j.val - 0 ≤ k),
      dite_eq_left h]
    exact congrArg x (Fin.ext (Nat.sub_zero _))
  · rw [dite_eq_right (by omega : ¬(0 ≤ j.val ∧ j.val - 0 ≤ k)),
      dite_eq_right h]

/-- Relabelling a family of faces along an injection `φ : Fin k ↪ Fin n`:
each face is transported by `Finset.map`. -/
def relabel (φ : Fin k ↪ Fin n) (D : Finset (Finset (Fin k))) :
    Finset (Finset (Fin n)) :=
  D.image fun s => s.map φ

/-- **`f`-vectors are invariant under relabelling the ground set**: `fEntry`
is unchanged by `relabel`, since `Finset.map` preserves cardinalities and is
injective.  The key lemma of `prop-permissive-fibres`. -/
theorem fEntry_relabel (φ : Fin k ↪ Fin n) (D : Finset (Finset (Fin k)))
    (j : ℕ) : fEntry (relabel φ D) j = fEntry D j := by
  rw [fEntry, fEntry, relabel, Finset.filter_image]
  have hpred : (D.filter fun s => #(s.map φ) = j) = D.filter fun s => #s = j := by
    apply Finset.filter_congr
    intro s _
    rw [Finset.card_map]
  rw [hpred, Finset.card_image_of_injective _ (Finset.map_injective φ)]

/-- Relabelling preserves the order-ideal property: a subset of a transported
face is itself transported (`Finset.subset_map_iff`), from a subset in the
source. -/
theorem isOrderIdeal_relabel (φ : Fin k ↪ Fin n)
    {D : Finset (Finset (Fin k))} (hD : IsOrderIdeal D) :
    IsOrderIdeal (relabel φ D) := by
  intro s t hs hts
  rw [relabel, Finset.mem_image] at hs ⊢
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.mp hts
  exact ⟨u, hD hs' hu, rfl⟩

/-- Relabelling preserves non-emptiness. -/
theorem relabel_nonempty {φ : Fin k ↪ Fin n} {D : Finset (Finset (Fin k))}
    (h : D.Nonempty) : (relabel φ D).Nonempty :=
  h.image _

/-- Relabelling transports the `f`-vector along `ι_k`: entries up to `k`
agree (`fEntry_relabel`), entries beyond `k` vanish on both sides (a face of
a family on `[k]` has at most `k` elements). -/
theorem fvec_relabel (φ : Fin k ↪ Fin n) (D : Finset (Finset (Fin k))) :
    fvec (relabel φ D) = iotaIncl n k (fvec D) := by
  funext j
  rw [iotaIncl_apply]
  show (fEntry (relabel φ D) j.val : ℝ) = _
  by_cases h : j.val ≤ k
  · rw [dite_eq_left h, fEntry_relabel]
    rfl
  · rw [dite_eq_right h, fEntry_relabel, fEntry_eq_zero_of_lt (by omega),
      Nat.cast_zero]

/-- The support (vertex set) of a family: `V = {i ∈ [n] : {i} ∈ Δ}`. -/
def support (D : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ({i} : Finset (Fin n)) ∈ D

/-- `|V| = f₁(Δ)`: the vertices biject with the faces of cardinality one. -/
theorem card_support (D : Finset (Finset (Fin n))) :
    #(support D) = fEntry D 1 := by
  rw [fEntry, ← Finset.card_image_of_injective (support D)
    Finset.singleton_injective]
  congr 1
  ext s
  simp only [Finset.mem_image, Finset.mem_filter, Finset.card_eq_one, support,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i, rfl⟩
  · rintro ⟨hs, i, rfl⟩
    exact ⟨i, hs, rfl⟩

/-- Downward closure puts every face inside the support: `σ ⊆ V` for
`σ ∈ Δ`. -/
theorem subset_support {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D)
    {s : Finset (Fin n)} (hs : s ∈ D) : s ⊆ support D := by
  intro i hi
  rw [support, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hD hs (Finset.singleton_subset_iff.mpr hi)⟩

/-- The heart of `prop-permissive-fibres`' proof: a non-empty order ideal on
`[n]` **is** a relabelled strict complex on `[k]`, `k = f₁(Δ)` — regarded as a
family on its support `V`, `Δ` contains `∅` and every singleton of `V`, and
transporting along the order isomorphism `[k] → V` (`Finset.orderEmbOfFin`)
is `relabel`.  (At `k = 0` this degenerates correctly: `V = ∅` forces
`Δ = {∅}` and `D' = {∅}` is the one complex on `[0]`.) -/
theorem exists_relabel {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D)
    (hne : D.Nonempty) :
    ∃ (φ : Fin (fEntry D 1) ↪ Fin n)
      (D' : Finset (Finset (Fin (fEntry D 1)))),
      IsComplex D' ∧ relabel φ D' = D := by
  classical
  have hcard : #(support D) = fEntry D 1 := card_support D
  set φ : Fin (fEntry D 1) ↪ Fin n :=
    ((support D).orderEmbOfFin hcard).toEmbedding with hφ
  have hφ_mem : ∀ i, φ i ∈ support D :=
    fun i => (support D).orderEmbOfFin_mem hcard i
  have hmapuniv : Finset.univ.map φ = support D := by
    apply Finset.coe_injective
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    exact (support D).range_orderEmbOfFin hcard
  set D' : Finset (Finset (Fin (fEntry D 1))) :=
    Finset.univ.filter (fun s' => s'.map φ ∈ D) with hD'
  have hrel : relabel φ D' = D := by
    ext s
    rw [relabel, Finset.mem_image]
    constructor
    · rintro ⟨s', hs', rfl⟩
      exact (Finset.mem_filter.mp hs').2
    · intro hs
      have hsub : s ⊆ Finset.univ.map φ := hmapuniv ▸ subset_support hD hs
      obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.mp hsub
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩
  refine ⟨φ, D', ⟨?_, ?_, ?_⟩, hrel⟩
  · intro s' t' hs' hts'
    rw [hD', Finset.mem_filter] at hs' ⊢
    exact ⟨Finset.mem_univ _, hD hs'.2 (Finset.map_subset_map.mpr hts')⟩
  · rw [hD', Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.map_empty]
    exact hD.empty_mem hne
  · intro i
    rw [hD', Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.map_singleton]
    have h := hφ_mem i
    rw [support, Finset.mem_filter] at h
    exact h.2

/-- `prop-permissive-fibres`, the partition equality `eq:permissive-fibres`:
`S_n⁺ = ⋃_{k=0}^n ι_k(S_k)` — every `f`-vector of a non-empty order ideal is
`ι_k` of the `f`-vector of a strict complex on `[k]`, `k = f₁`, and
conversely.  Stated for all `n ≥ 0`, as the manuscript does; disjointness of
the blocks is `fibres_disjoint`. -/
theorem permissive_fibres (n : ℕ) :
    SsetPerm n = ⋃ k ∈ Set.Icc 0 n, iotaIncl n k '' Sset k := by
  ext x
  rw [Set.mem_iUnion₂]
  constructor
  · rintro ⟨D, hD, hne, rfl⟩
    obtain ⟨φ, D', hD', hrel⟩ := exists_relabel hD hne
    refine ⟨fEntry D 1, Set.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩,
      fvec D', ⟨D', hD', rfl⟩, ?_⟩
    · have h := fEntry_le_choose D 1
      rwa [Nat.choose_one_right] at h
    · exact (fvec_relabel φ D').symm.trans (congrArg fvec hrel)
  · rintro ⟨k, hk, -, ⟨D', hD', rfl⟩, rfl⟩
    exact ⟨relabel (Fin.castLEEmb (Set.mem_Icc.mp hk).2) D',
      isOrderIdeal_relabel _ hD'.ideal, relabel_nonempty hD'.nonempty,
      (fvec_relabel _ _)⟩

/-- On the block `ι_k(S_k)` the coordinate `x₁` is constantly `k` — the
manuscript's "an element of `ι_k(S_k)` has first coordinate `f₁ = k`".  (For
`k ≥ 1` this is properness of the complex on `[k]`; for `k = 0` the appended
zeros give it.) -/
theorem apply_one_of_mem_fibre (hn : 1 ≤ n) {k : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ iotaIncl n k '' Sset k) : x 1 = (k : ℝ) := by
  obtain ⟨y, ⟨D, hD, rfl⟩, rfl⟩ := hx
  rw [fin_one_eq hn, iotaIncl_apply]
  by_cases hk1 : 1 ≤ k
  · rw [dite_eq_left hk1]
    show (fEntry D (1 : ℕ) : ℝ) = (k : ℝ)
    rw [fEntry_one hD]
  · rw [dite_eq_right hk1]
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.cast_zero]

/-- `prop-permissive-fibres`, disjointness: distinct blocks are disjoint,
because `x₁` determines `k`.  (No `n ≥ 1` hypothesis: two distinct `k, l ≤ n`
force `n ≥ 1`.) -/
theorem fibres_disjoint {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) (hkl : k ≠ l) :
    Disjoint (iotaIncl n k '' Sset k) (iotaIncl n l '' Sset l) := by
  have hn : 1 ≤ n := by omega
  rw [Set.disjoint_left]
  intro x hxk hxl
  have h1 := apply_one_of_mem_fibre hn hxk
  have h2 := apply_one_of_mem_fibre hn hxl
  exact hkl (by exact_mod_cast h1.symm.trans h2)

/-- `prop-permissive-fibres`, fibre form: "the part with `f₁ = k` being
exactly `ι_k(S_k)`". -/
theorem fibre_eq (hn : 1 ≤ n) {k : ℕ} (hk : k ≤ n) :
    iotaIncl n k '' Sset k = {x ∈ SsetPerm n | x 1 = (k : ℝ)} := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, apply_one_of_mem_fibre hn hx⟩
    rw [permissive_fibres]
    exact Set.mem_biUnion (Set.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩) hx
  · rintro ⟨hx, hx1⟩
    rw [permissive_fibres, Set.mem_iUnion₂] at hx
    obtain ⟨l, -, hxl⟩ := hx
    have hlk : (l : ℝ) = (k : ℝ) := by
      rw [← apply_one_of_mem_fibre hn hxl, hx1]
    have : l = k := by exact_mod_cast hlk
    subst this
    exact hxl

/-- The manuscript's `k = 0` degeneration check: `𝒮₀ = {{∅}}` gives
`S₀ = {(1)}`. -/
theorem Sset_zero : Sset 0 = {(fun _ => 1 : Fin 1 → ℝ)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨D, hD, rfl⟩
    funext j
    show (fEntry D j.val : ℝ) = 1
    have hj : j.val = 0 := by omega
    rw [hj, fEntry_zero hD.ideal hD.nonempty, Nat.cast_one]
  · rintro rfl
    refine ⟨{∅}, ⟨isOrderIdeal_singleton_empty, Finset.mem_singleton_self _,
      fun i => i.elim0⟩, ?_⟩
    funext j
    show (fEntry ({∅} : Finset (Finset (Fin 0))) j.val : ℝ) = 1
    have hj : j.val = 0 := by omega
    rw [hj, fEntry_zero isOrderIdeal_singleton_empty
      ⟨∅, Finset.mem_singleton_self _⟩, Nat.cast_one]

/-- The manuscript's `k = 0` degeneration check, concluded:
`ι₀(S₀) = {e₀}` — the single point of the bottom block. -/
theorem fibre_zero (n : ℕ) : iotaIncl n 0 '' Sset 0 = {e0 n} := by
  rw [Sset_zero, Set.image_singleton]
  congr 1
  funext j
  simp only [iotaIncl_apply, e0]
  by_cases h : j.val ≤ 0
  · rw [dite_eq_left h, ite_eq_left (by omega : j.val = 0)]
  · rw [dite_eq_right h, ite_eq_right (by omega : ¬(j.val = 0))]

end ExteriorConvex
