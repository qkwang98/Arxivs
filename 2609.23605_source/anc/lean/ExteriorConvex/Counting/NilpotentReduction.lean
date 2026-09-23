/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The binomial reduction and the staircase corner evaluation, in general

The two general facts behind `thm-delta0-degrees`
(`working-notes/delta0-exact-degrees-proof.org`, §"The reduction" and
§"Corner evaluation"), stated as the working note states them — for an
*arbitrary* matrix over an arbitrary commutative ring, with arbitrary
vectors `v⃗`, `w⃗` — rather than for the concrete `Nmat n` of rung D2:

* **The reduction** (`vecMul_one_add_pow_dotProduct`): for `M = I + N`,
  `v⃗ M^r w⃗ = ∑_{k=0}^{r} C(r,k) · (v⃗ N^k w⃗)` — the binomial theorem for
  the commuting pair `(1, N)`, pushed through the bilinear sandwich.  No
  nilpotency is needed for this finite form; nilpotency (or any eventual
  vanishing of the brackets `v⃗ N^k w⃗`) enters only through the range
  change `sum_range_choose_mul_of_eventually_zero`.
* **The corner evaluation** (`pow_apply_staircase_of_strictUpper`): if `N`
  is strictly upper triangular on `Fin m`, then `N^k` vanishes below the
  `k`-th superdiagonal (`pow_apply_eq_zero_of_strictUpper`, whence
  `N^m = 0`, `pow_eq_zero_of_strictUpper`), and **on** the `k`-th
  superdiagonal `(N^k)[i][i+k]` is the product of the `k` superdiagonal
  entries along the staircase from `i` to `i+k` — a non-zero term in the
  expansion of the power needs a strictly increasing walk of `k` steps,
  and the exact superdiagonal position leaves only the full staircase.
  The superdiagonal entries are supplied through a total function
  `g : ℕ → R` (hypothesis `hg`), so that the product needs no dependent
  index bounds.

Rung D2's concrete versions (`Nmat_pow_apply_eq_zero`,
`Nmat_pow_staircase` in `Counting/Delta0.lean`) are re-derived from these;
rung D3's proper layer applies the same lemmas to the principal block
`B` of `T′(0)` (`Counting/ProperBlock.lean`), which is the reason for the
generality — the manuscript's proof of `thm-delta0-degrees` states both
facts generically in prose and applies them twice, and after this
refactor the Lean does the same.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`).
-/
import Mathlib

open Finset Matrix

namespace ExteriorConvex

variable {R : Type*} [CommRing R]

/-! ## The reduction: `v⃗ (I+N)^r w⃗ = ∑ₖ C(r,k) (v⃗ N^k w⃗)` -/

section Reduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bilinear sandwich of `N^m` scaled by a ℕ-cast scalar matrix:
the scalar comes out front. -/
theorem vecMul_pow_natCast_mul_dotProduct (N : Matrix ι ι R) (v w : ι → R)
    (m c : ℕ) :
    v ᵥ* (N ^ m * (c : Matrix ι ι R)) ⬝ᵥ w =
      (c : R) * (v ᵥ* N ^ m ⬝ᵥ w) := by
  rw [show ((c : ℕ) : Matrix ι ι R) = c • (1 : Matrix ι ι R) from by
    rw [nsmul_eq_mul, mul_one]]
  rw [mul_smul_comm, mul_one, Matrix.vecMul_smul, smul_dotProduct,
    nsmul_eq_mul]

/-- **The reduction** (the working note's "*Let `M` be any square matrix
of the form `M = I + N` … let `v⃗`, `w⃗` be any vectors*"), finite form:
`v⃗ (I+N)^r w⃗ = ∑_{k=0}^{r} C(r,k) · (v⃗ N^k w⃗)`.  The binomial theorem
for the commuting pair `(1, N)`; no nilpotency hypothesis. -/
theorem vecMul_one_add_pow_dotProduct (N : Matrix ι ι R) (v w : ι → R)
    (r : ℕ) :
    v ᵥ* (1 + N) ^ r ⬝ᵥ w =
      ∑ k ∈ Finset.range (r + 1), (r.choose k : R) * (v ᵥ* N ^ k ⬝ᵥ w) := by
  rw [add_comm (1 : Matrix ι ι R) N, (Commute.one_right N).add_pow r]
  simp only [one_pow, mul_one]
  rw [Matrix.vecMul_sum, sum_dotProduct]
  exact Finset.sum_congr rfl fun m _ =>
    vecMul_pow_natCast_mul_dotProduct N v w m (r.choose m)

/-- Truncation/extension of the binomial range against an eventually-zero
bracket sequence: below `r + 1` the binomial coefficient vanishes, from
`m` on the bracket does.  This is where nilpotency of `N` is spent when
the reduction is applied. -/
theorem sum_range_choose_mul_of_eventually_zero {m : ℕ} {b : ℕ → R}
    (hb : ∀ k, m ≤ k → b k = 0) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (r.choose k : R) * b k =
      ∑ k ∈ Finset.range m, (r.choose k : R) * b k := by
  rcases le_total (r + 1) m with h | h
  · refine Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) h))
      fun k hk hk' => ?_
    rw [Finset.mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  · refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) h))
      fun k hk hk' => ?_).symm
    rw [Finset.mem_range] at hk hk'
    rw [hb k (by omega), mul_zero]

end Reduction

/-! ## The corner evaluation: strictly upper triangular powers -/

section Staircase

variable {m : ℕ} {N : Matrix (Fin m) (Fin m) R}

/-- Powers of a strictly upper triangular matrix climb: `N^k` vanishes
below the `k`-th superdiagonal.  (Each factor of `N` moves the column
index up by at least one.) -/
theorem pow_apply_eq_zero_of_strictUpper
    (hN : ∀ i j : Fin m, j.val ≤ i.val → N i j = 0) :
    ∀ (k : ℕ) {i j : Fin m}, j.val < i.val + k → (N ^ k) i j = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j h
    rw [pow_zero]
    exact Matrix.one_apply_ne fun hcon => by subst hcon; omega
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l.val (i.val + k) with hl | hl
    · rw [ih hl, zero_mul]
    · rw [hN l j (by omega), mul_zero]

/-- A strictly upper triangular matrix on `Fin m` is nilpotent of order
at most `m`. -/
theorem pow_eq_zero_of_strictUpper
    (hN : ∀ i j : Fin m, j.val ≤ i.val → N i j = 0) : N ^ m = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact pow_apply_eq_zero_of_strictUpper hN m (by have := j.isLt; omega)

/-- **The corner evaluation** (the working note's "*If `N` is strictly
upper triangular with respect to the ordered index set…*"): on the exact
`k`-th superdiagonal, `(N^k)[i][i+k]` is the product of the superdiagonal
entries along the staircase — only the full staircase walk survives.  The
superdiagonal is supplied as a total function `g` (hypothesis `hg`) so
the product carries no dependent index bounds. -/
theorem pow_apply_staircase_of_strictUpper
    (hN : ∀ i j : Fin m, j.val ≤ i.val → N i j = 0) {g : ℕ → R}
    (hg : ∀ (a : ℕ) (h1 : a < m) (h2 : a + 1 < m), N ⟨a, h1⟩ ⟨a + 1, h2⟩ = g a) :
    ∀ (k : ℕ) {i j : Fin m}, j.val = i.val + k →
      (N ^ k) i j = ∏ a ∈ Finset.range k, g (i.val + a) := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have hij : i = j := Fin.ext (by omega)
    rw [pow_zero, ← hij, Matrix.one_apply_eq, Finset.range_zero,
      Finset.prod_empty]
  | succ k ih =>
    intro i j h
    have hik : i.val + k < m := by have := j.isLt; omega
    rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_eq_single_of_mem (⟨i.val + k, hik⟩ : Fin m)
        (Finset.mem_univ _) (fun l _ hne => by
      rcases lt_or_ge l.val (i.val + k) with hl | hl
      · rw [pow_apply_eq_zero_of_strictUpper hN k hl, zero_mul]
      · have hlv : l.val ≠ i.val + k := fun hc => hne (Fin.ext hc)
        rw [hN l j (by omega), mul_zero])]
    have h1 : (N ^ k) i ⟨i.val + k, hik⟩ =
        ∏ a ∈ Finset.range k, g (i.val + a) := ih rfl
    have hjm : i.val + k + 1 < m := by have := j.isLt; omega
    have h2 : N ⟨i.val + k, hik⟩ j = g (i.val + k) := by
      have hj_eq : j = ⟨i.val + k + 1, hjm⟩ := Fin.ext (by omega)
      rw [hj_eq]
      exact hg (i.val + k) hik hjm
    rw [h1, h2, Finset.prod_range_succ]

end Staircase

end ExteriorConvex
