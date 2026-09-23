/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Rung D3b of the article-2 formalisation: the invariant-block repair

Formalisation of the "Restriction to the invariant block" step of the
proper half of `thm-delta0-degrees`, from
`working-notes/delta0-exact-degrees-proof.org` (§"Proof of Theorem 2",
under "*Caveat: the naive reduction fails here*"), per
`working-notes/PLAN-formalise-article2.org` (rung D3b).  This is the
genuinely new mathematics of rung D3 — there is no improper analogue.

**The caveat, certified**: `T′(0)` is *not* unipotent on the full index
set `{−1, …, n}`.  Its columns `τ′ = −1` and `τ′ = 0` vanish identically
(`Tpmat_apply_eq_zero_of_le_one`, from `Apmat_eq_zero_of_le_zero`: row
`−1` of `A` lives in column `ρ = 0`, row `0` in column `ρ = 1`, both
zeroed in `A′`), so `T′(0) − I` is not nilpotent and the reduction of
`NilpotentReduction.lean` cannot be applied on `Fin (n+2)`.  (That
*exactly* these two columns vanish, and no more: `Bmat_diag` below gives
`T′(0)[τ][τ] = 1 ≠ 0` for every `τ ≥ 1`.)

**The repair, formalised**:

* `u⃗′` is supported on `τ ≥ 1` (`upVec_eq_zero_of_le_one`: its `−1` and
  `0` entries are row sums of zeroed-out rows);
* columns `−1` and `0` of `T′(δ)` vanish — for *every* `δ`, a mild
  strengthening of the note's `δ = 0` claim
  (`vecMul_Tpmat_eq_zero_of_le_one`: `v⃗ T′(δ)` is supported on
  `{1, …, n}` for **any** `v⃗`);
* hence every product `u⃗′ T′(0)^k` stays supported on `{1, …, n}` and
  equals `ũ⃗ B^k` on the principal block `B = Bmat n` of `T′(0)` with
  rows and columns in `τ ∈ {1, …, n}` (`vecMul_Tpmat_zero_pow_block`),
  and dotting with `1⃗` loses nothing since the discarded coordinates
  are zero (`vecMul_Tpmat_zero_pow_dot_block`);
* **`B` is unipotent**: it inherits upper triangularity
  (`Bmat_eq_zero_of_lt`), and `B[τ][τ] = A′[τ][τ+1] = A[τ][τ+1] = 1` for
  `τ ≥ 1` (`Bmat_diag`), the zeroing of columns `ρ ≤ 1` not touching
  `ρ = τ+1 ≥ 2`; over ℚ, `N′ = B − I` is strictly upper triangular
  (`NBmat_apply_eq_zero_of_le`) with `N′^n = 0` (`NBmat_pow_eq_zero`, by
  the general `pow_eq_zero_of_strictUpper` — the second consumer of the
  refactored general lemmas, after `Nmat`).

**The conclusion, in the form rung D3d will consume**
(`card_properChainedTuples_of_gaps_eq_zero`): with all gaps zero, the
proper count of rank `r + 1` is `ũ⃗ B^r 1⃗` on an `n × n` block — the
note's `a′_r = ũ⃗ B^{r−1} 1⃗` with the manuscript's rank equal to the gap
count plus one — with `B` unipotent and with the superdiagonal
`B[τ][τ+1] = C(n, τ+1)` (`Bmat_superdiag`/`NBmat_superdiag` — both
column indices are `≥ 2`, so the zeroing is invisible and Lemma A
applies verbatim) ready for D3d's corner evaluation.

**Out of scope, deliberately**: rung D3d (the exact degree `n − 1`, the
leading coefficient `(∏_{j=2}^n C(n,j))/(n−1)!`, `u′[1] = 1`) and rung
D3c (`prop-proper-threshold`, `λ_pr`).

The index bookkeeping is one embedding: `blockEmb i = i + 2` maps the
block index `i : Fin n` to the matrix index `k : Fin (n+2)`, i.e. block
row `i` is the `tp`-class `τ = i + 1 ∈ {1, …, n}`.

**`native_decide` is banned in this development** (it would add the axiom
`Lean.ofReduceBool`); the anchors — at `n = 2` the block sandwiches
`ũ⃗ B^r 1⃗` against `|FF_pr(2;0^{r+1})| = r + 2`, at `n = 3` the values
`5, 12, 45, 51` against `|S_3|`, `rem-proper-sequences` and
`eq:proper-not-reversible` — were `#eval`s during development (recorded
in `runs/proper-lean-anchors-20260918.md`) and stay out of the formal
statements, deliberately.
-/
import ExteriorConvex.Counting.Proper
import ExteriorConvex.Counting.Structure
import ExteriorConvex.Counting.NilpotentReduction

open Finset Matrix

namespace ExteriorConvex

variable {n : ℕ}

/-! ## The caveat: `u⃗′` and the columns of `T′(δ)` vanish on `τ ≤ 0` -/

/-- `u⃗′` is supported on `τ ≥ 1`: its `−1` and `0` entries are row sums
of the zeroed-out rows of `A′`. -/
theorem upVec_eq_zero_of_le_one {k : Fin (n + 2)} (h : k.val ≤ 1) :
    upVec n k = 0 := by
  simp only [upVec]
  exact Finset.sum_eq_zero fun ρ _ =>
    Apmat_eq_zero_of_le_zero (by simp only [tauOf]; omega)

/-- Columns `τ′ = −1` and `τ′ = 0` of `T′(δ)` vanish identically — for
*every* `δ`, not only `δ = 0` (the entry reads row `τ′` of `A′`, which
vanishes; the gap enters only the `ρ`-range). -/
theorem Tpmat_apply_eq_zero_of_le_one (δ : ℤ) (k : Fin (n + 2))
    {k' : Fin (n + 2)} (h : k'.val ≤ 1) :
    Tpmat n δ k k' = 0 := by
  rw [Tpmat_apply]
  exact Finset.sum_eq_zero fun ρ _ =>
    Apmat_eq_zero_of_le_zero (by simp only [tauOf]; omega)

/-- Any row vector through `T′(δ)` lands supported on `{1, …, n}`: the
coordinates `−1` and `0` of `v⃗ T′(δ)` vanish for **any** `v⃗`. -/
theorem vecMul_Tpmat_eq_zero_of_le_one (δ : ℤ) (v : Fin (n + 2) → ℕ)
    {k' : Fin (n + 2)} (h : k'.val ≤ 1) :
    (v ᵥ* Tpmat n δ) k' = 0 := by
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_eq_zero fun k _ => by
    rw [Tpmat_apply_eq_zero_of_le_one δ k h, mul_zero]

/-! ## The principal block `B` on `τ ∈ {1, …, n}` -/

/-- The block embedding: block index `i : Fin n` to matrix index
`i + 2 : Fin (n+2)`, i.e. the `tp`-class `τ = i + 1 ∈ {1, …, n}`. -/
def blockEmb (n : ℕ) : Fin n → Fin (n + 2) :=
  fun i => ⟨i.val + 2, by omega⟩

@[simp] theorem blockEmb_val (n : ℕ) (i : Fin n) :
    (blockEmb n i).val = i.val + 2 := rfl

/-- The principal block `B` of `T′(0)` with rows and columns in
`τ ∈ {1, …, n}`. -/
def Bmat (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  (Tpmat n 0).submatrix (blockEmb n) (blockEmb n)

theorem Bmat_apply (n : ℕ) (i j : Fin n) :
    Bmat n i j = Tpmat n 0 (blockEmb n i) (blockEmb n j) := rfl

/-- `ũ⃗ = (u′[1], …, u′[n])`, the restriction of `u⃗′` to its support. -/
def uTilde (n : ℕ) : Fin n → ℕ := fun i => upVec n (blockEmb n i)

/-- Splitting a sum over `Fin (n+2)` into the two boundary indices and
the block. -/
theorem sum_univ_split_block {M : Type*} [AddCommMonoid M]
    (f : Fin (n + 2) → M) :
    ∑ k, f k = f 0 + f 1 + ∑ j : Fin n, f (blockEmb n j) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ← add_assoc,
    Fin.succ_zero_eq_one]
  rfl

/-! ## The restriction to the invariant block -/

/-- The invariant-block restriction, entrywise, by induction on the
power: every product `u⃗′ T′(0)^r` (a) vanishes on the coordinates `−1`
and `0`, and (b) agrees with `ũ⃗ B^r` on the block. -/
theorem vecMul_Tpmat_zero_pow_block (n : ℕ) : ∀ r : ℕ,
    (∀ k' : Fin (n + 2), k'.val ≤ 1 →
      (upVec n ᵥ* Tpmat n 0 ^ r) k' = 0) ∧
    (∀ i : Fin n, (upVec n ᵥ* Tpmat n 0 ^ r) (blockEmb n i) =
      (uTilde n ᵥ* Bmat n ^ r) i) := by
  intro r
  induction r with
  | zero =>
    refine ⟨fun k' h => ?_, fun i => ?_⟩
    · rw [pow_zero, Matrix.vecMul_one]
      exact upVec_eq_zero_of_le_one h
    · rw [pow_zero, pow_zero, Matrix.vecMul_one, Matrix.vecMul_one]
      rfl
  | succ r ih =>
    obtain ⟨ihz, ihb⟩ := ih
    have hstep : upVec n ᵥ* Tpmat n 0 ^ (r + 1) =
        (upVec n ᵥ* Tpmat n 0 ^ r) ᵥ* Tpmat n 0 := by
      rw [pow_succ, Matrix.vecMul_vecMul]
    have hva : ∀ (v : Fin (n + 2) → ℕ) (k' : Fin (n + 2)),
        (v ᵥ* Tpmat n 0) k' = ∑ k, v k * Tpmat n 0 k k' :=
      fun v k' => rfl
    have hvb : ∀ (v : Fin n → ℕ) (i : Fin n),
        (v ᵥ* Bmat n) i = ∑ j, v j * Bmat n j i :=
      fun v i => rfl
    refine ⟨fun k' h => ?_, fun i => ?_⟩
    · rw [hstep]
      exact vecMul_Tpmat_eq_zero_of_le_one 0 _ h
    · rw [hstep, hva, pow_succ, ← Matrix.vecMul_vecMul, hvb]
      rw [sum_univ_split_block
        (fun k => (upVec n ᵥ* Tpmat n 0 ^ r) k * Tpmat n 0 k (blockEmb n i))]
      rw [ihz 0 (by simp), ihz 1 (by simp), zero_mul, zero_mul, add_zero,
        zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ihb j, Bmat_apply]

/-- **The invariant-block restriction, sandwiched** (the note's "dotting
with `1⃗` loses nothing since the discarded coordinates are zero"):
`u⃗′ T′(0)^r 1⃗` on `Fin (n+2)` equals `ũ⃗ B^r 1⃗` on the `n × n` block. -/
theorem vecMul_Tpmat_zero_pow_dot_block (n r : ℕ) :
    upVec n ᵥ* Tpmat n 0 ^ r ⬝ᵥ onesCol n =
      uTilde n ᵥ* Bmat n ^ r ⬝ᵥ (fun _ => (1 : ℕ)) := by
  obtain ⟨hz, hb⟩ := vecMul_Tpmat_zero_pow_block n r
  have hL : upVec n ᵥ* Tpmat n 0 ^ r ⬝ᵥ onesCol n =
      ∑ k, (upVec n ᵥ* Tpmat n 0 ^ r) k := dotProduct_onesCol _
  have hR : uTilde n ᵥ* Bmat n ^ r ⬝ᵥ (fun _ => (1 : ℕ)) =
      ∑ j, (uTilde n ᵥ* Bmat n ^ r) j := by
    simp [dotProduct]
  rw [hL, hR,
    sum_univ_split_block (fun k => (upVec n ᵥ* Tpmat n 0 ^ r) k),
    hz 0 (by simp), hz 1 (by simp), zero_add, zero_add]
  exact Finset.sum_congr rfl fun j _ => hb j

/-- With every gap zero the proper transfer product collapses to a
power (the `T′` analogue of `Tprod_zero_gaps`). -/
theorem Tpprod_zero_gaps (n : ℕ) :
    ∀ r : ℕ, Tpprod n r (fun _ => (0 : ℤ)) = Tpmat n 0 ^ r := by
  intro r
  induction r with
  | zero => rw [Tpprod_zero, pow_zero]
  | succ r ih =>
    show Tpprod n r (fun _ => (0 : ℤ)) * Tpmat n 0 = Tpmat n 0 ^ (r + 1)
    rw [ih, pow_succ]

/-- **D3b, the conclusion in the form D3d will consume**: with all gaps
zero, the proper chained count of rank `r + 1` (`r` gaps) is
`ũ⃗ B^r 1⃗` on the `n × n` principal block.  Unconditional — not even
`n ≥ 1` (at `n = 0` both sides are `0`: the block is empty and so is the
proper locus). -/
theorem card_properChainedTuples_of_gaps_eq_zero (n r : ℕ)
    {d : Fin (r + 1) → ℕ} (hd : gaps d = fun _ => (0 : ℤ)) :
    #(properChainedTuples n (r + 1) d) =
      uTilde n ᵥ* Bmat n ^ r ⬝ᵥ (fun _ => (1 : ℕ)) := by
  rw [card_properChainedTuples, hd, Tpprod_zero_gaps,
    vecMul_Tpmat_zero_pow_dot_block]

/-! ## `B` is unipotent

Upper triangularity is inherited from `T′(0)`; the diagonal is the
untouched superdiagonal of `A`.  Over ℚ, `N′ = B − I` is strictly upper
triangular, hence `N′^n = 0` by the general lemma — `T′(0)` itself fails
this on `Fin (n+2)`, which is the whole point of the block. -/

/-- Row form of `T′(0)`: the `ρ`-range `{0, …, n+1} ∩ {ρ > τ}` is
`{k, …, n+1}` in the `Fin (n+2)` indexing (the `T′` analogue of
`Tmat_zero_apply_eq_sum`). -/
theorem Tpmat_zero_apply_eq_sum (k k' : Fin (n + 2)) :
    Tpmat n 0 k k' =
      ∑ ρ ∈ Finset.Icc (k.val : ℤ) ((n : ℤ) + 1), Apmat n (tauOf k') ρ := by
  rw [Tpmat_apply]
  congr 1
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_Icc, tauOf, sub_zero]
  omega

/-- `T′(0)` is upper triangular in the `tp`-ordering, like `T(0)`: a
non-zero entry needs `τ + 1 ≤ ρ ≤ τ' + 1`. -/
theorem Tpmat_zero_eq_zero_of_lt {k k' : Fin (n + 2)} (h : k' < k) :
    Tpmat n 0 k k' = 0 := by
  rw [Tpmat_zero_apply_eq_sum]
  refine Finset.sum_eq_zero fun ρ hρ => ?_
  rw [Finset.mem_Icc] at hρ
  refine Apmat_eq_zero_of_add_one_lt ?_
  have hlt : k'.val < k.val := h
  simp only [tauOf]
  omega

/-- `B` inherits upper triangularity. -/
theorem Bmat_eq_zero_of_lt {i j : Fin n} (h : j < i) : Bmat n i j = 0 := by
  rw [Bmat_apply]
  refine Tpmat_zero_eq_zero_of_lt ?_
  have hlt : j.val < i.val := h
  rw [Fin.lt_def]
  simp only [blockEmb_val]
  omega

/-- **The unit diagonal of `B`**: `B[τ][τ] = A′[τ][τ+1] = A[τ][τ+1] = 1`
for `τ = i + 1 ≥ 1` — on the diagonal only `ρ = τ + 1` survives, and
`ρ = τ + 1 ≥ 2` is untouched by the zeroing, so D1's superdiagonal
rigidity applies verbatim.  (Contrast rows `τ ≤ 0` of `T′(0)`, whose
diagonal entries are `0`: this is where `T′(0)` fails unipotence and `B`
recovers it.) -/
theorem Bmat_diag (n : ℕ) (i : Fin n) : Bmat n i i = 1 := by
  have hin := i.isLt
  rw [Bmat_apply, Tpmat_zero_apply_eq_sum]
  rw [Finset.sum_eq_single_of_mem ((blockEmb n i).val : ℤ)
      (Finset.mem_Icc.mpr ⟨le_refl _, by simp only [blockEmb_val]; omega⟩)
      (fun ρ hρ hne => by
        rw [Finset.mem_Icc] at hρ
        simp only [blockEmb_val] at hρ hne
        refine Apmat_eq_zero_of_add_one_lt ?_
        simp only [tauOf, blockEmb_val]
        omega)]
  have hτ : tauOf (blockEmb n i) = ((i.val + 1 : ℕ) : ℤ) := by
    simp only [tauOf, blockEmb_val]
    push_cast
    ring
  have hρv : ((blockEmb n i).val : ℤ) = ((i.val + 1 : ℕ) : ℤ) + 1 := by
    simp only [blockEmb_val]
    push_cast
    ring
  rw [hτ, hρv, Apmat_eq_of_le (by push_cast; omega),
    Amat_superdiag n (show i.val + 1 ≤ n by omega)]

/-- The superdiagonal of `B`: `B[τ][τ+1] = A′[τ+1][τ+1] + A′[τ+1][τ+2] =
A[τ+1][τ+1] + A[τ+1][τ+2] = C(n, τ+1)` for `τ = i + 1` — both column
indices are `≥ 2`, so the zeroing is invisible and the two-term sum of
`eq:delta0-superdiag` applies verbatim.  In block indices the entry at
`(i, i+1)` is `C(n, i+2)`.  This is the input to rung D3d's corner
evaluation. -/
theorem Bmat_superdiag {i : ℕ} (hi : i + 1 < n) :
    Bmat n ⟨i, by omega⟩ ⟨i + 1, hi⟩ = n.choose (i + 2) := by
  have hj : i + 2 ≤ n := by omega
  rw [Bmat_apply, Tpmat_zero_apply_eq_sum]
  have hτ : tauOf (blockEmb n ⟨i + 1, hi⟩) = ((i + 2 : ℕ) : ℤ) := by
    simp only [tauOf, blockEmb_val]
    push_cast
    ring
  rw [hτ]
  have hsub : ({((i + 2 : ℕ) : ℤ), ((i + 2 : ℕ) : ℤ) + 1} : Finset ℤ) ⊆
      Finset.Icc ((blockEmb n (⟨i, by omega⟩ : Fin n)).val : ℤ)
        ((n : ℤ) + 1) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    rw [Finset.mem_Icc]
    simp only [blockEmb_val]
    rcases hρ with rfl | rfl <;> constructor <;> push_cast <;> omega
  rw [← Finset.sum_subset hsub (fun ρ hρ hρ' => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ'
    rw [Finset.mem_Icc] at hρ
    simp only [blockEmb_val] at hρ
    refine Apmat_eq_zero_of_add_one_lt ?_
    push_cast at hρ hρ' ⊢
    omega)]
  rw [Finset.sum_pair
    (show ((i + 2 : ℕ) : ℤ) ≠ ((i + 2 : ℕ) : ℤ) + 1 by omega)]
  rw [Apmat_eq_of_le (by push_cast; omega),
    Apmat_eq_of_le (by push_cast; omega), Amat_diag n hj,
    Amat_superdiag n hj]
  have := Nat.choose_pos hj
  omega

/-! ### `N′ = B − I` over ℚ -/

/-- `N′ = B − I` over ℚ: the strictly-upper-triangular part of the
unipotent block `B` (cast once, exactly as `Nmat` is from `T(0)`). -/
def NBmat (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  (Bmat n).map (Nat.cast : ℕ → ℚ) - 1

/-- The ℚ-cast of `B` is `I + N′`. -/
theorem map_Bmat_eq (n : ℕ) :
    (Bmat n).map (Nat.cast : ℕ → ℚ) = NBmat n + 1 := by
  rw [NBmat]
  abel

/-- `N′` is strictly upper triangular: entries on and below the diagonal
vanish. -/
theorem NBmat_apply_eq_zero_of_le {i j : Fin n} (h : j.val ≤ i.val) :
    NBmat n i j = 0 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · have hij : j = i := Fin.ext heq
    subst hij
    simp [NBmat, Matrix.sub_apply, Matrix.map_apply, Bmat_diag,
      Matrix.one_apply_eq]
  · have hne : i ≠ j := fun hc => by subst hc; omega
    simp [NBmat, Matrix.sub_apply, Matrix.map_apply,
      Bmat_eq_zero_of_lt (Fin.lt_def.mpr hlt), Matrix.one_apply_ne hne]

/-- **`B` is unipotent**: `N′^n = 0` — the general
`pow_eq_zero_of_strictUpper` applied to the block, which is what the
restriction bought (on `Fin (n+2)`, `T′(0) − I` is *not* nilpotent). -/
theorem NBmat_pow_eq_zero (n : ℕ) : NBmat n ^ n = 0 :=
  pow_eq_zero_of_strictUpper fun _i _j h => NBmat_apply_eq_zero_of_le h

/-- `B` is unipotent, packaged. -/
theorem isNilpotent_NBmat (n : ℕ) : IsNilpotent (NBmat n) :=
  ⟨n, NBmat_pow_eq_zero n⟩

/-- The superdiagonal of `N′` is the superdiagonal of `B`:
`C(n, i+2)` at block position `(i, i+1)` — D3d's staircase input. -/
theorem NBmat_superdiag {i : ℕ} (hi : i + 1 < n) :
    NBmat n ⟨i, by omega⟩ ⟨i + 1, hi⟩ = (n.choose (i + 2) : ℚ) := by
  have hne : (⟨i, by omega⟩ : Fin n) ≠ ⟨i + 1, hi⟩ := by
    intro hcon
    have hval := congrArg Fin.val hcon
    simp only at hval
    omega
  simp [NBmat, Matrix.sub_apply, Matrix.map_apply, Bmat_superdiag hi,
    Matrix.one_apply_ne hne]

end ExteriorConvex
