import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Character projectors from explicit convolution identities

The analytic conclusion here is unconditional once the stated finite-group
coefficient identities are supplied: an inverse-compatible convolution
idempotent gives a Hermitian positive semidefinite matrix under a unitary
matrix representation. For an ordinary character, supplying its genuine
convolution identity remains a separate representation-theory obligation.
-/

namespace Bridge.CharacterProjector

open scoped BigOperators
open scoped ComplexOrder
open Matrix

noncomputable section

variable {G : Type*} [Group G] [Fintype G]
variable {N : Type*} [Fintype N]

def weightedOperator (U : G → Matrix N N ℂ) (c : G → ℂ) : Matrix N N ℂ :=
  ∑ g : G, c g • U g

def convolution (c d : G → ℂ) (k : G) : ℂ :=
  ∑ g : G, c g * d (g⁻¹ * k)

omit [Group G] in
theorem weightedOperator_trace (U : G → Matrix N N ℂ) (c : G → ℂ) :
    Matrix.trace (weightedOperator U c) = ∑ g : G, c g * Matrix.trace (U g) := by
  simp [weightedOperator, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

theorem weightedOperator_mul (U : G → Matrix N N ℂ)
    (hU : ∀ g h, U (g * h) = U g * U h) (c d : G → ℂ) :
    weightedOperator U c * weightedOperator U d =
      weightedOperator U (convolution c d) := by
  unfold weightedOperator convolution
  calc
    (∑ g : G, c g • U g) * (∑ h : G, d h • U h) =
        ∑ g : G, ∑ h : G, (c g * d h) • U (g * h) := by
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, hU]
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ k : G, (c g * d (g⁻¹ * k)) • U k := by
      apply Finset.sum_congr rfl
      intro g hg
      apply Fintype.sum_equiv (Equiv.mulLeft g)
      intro h
      simp
    _ = ∑ k : G, (∑ g : G, c g * d (g⁻¹ * k)) • U k := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]

theorem weightedOperator_idempotent (U : G → Matrix N N ℂ)
    (hU : ∀ g h, U (g * h) = U g * U h) (c : G → ℂ)
    (hc : ∀ k, convolution c c k = c k) :
    weightedOperator U c * weightedOperator U c = weightedOperator U c := by
  rw [weightedOperator_mul U hU]
  have heq : convolution c c = c := funext hc
  rw [heq]

/-- A class coefficient gives a central operator in the represented group
algebra. This also supplies commutation with projectors from subgroups. -/
theorem weightedOperator_commutes (U : G → Matrix N N ℂ)
    (hU : ∀ g h, U (g * h) = U g * U h) (c : G → ℂ)
    (hc : ∀ a g, c (a⁻¹ * g * a) = c g) (a : G) :
    Commute (weightedOperator U c) (U a) := by
  change weightedOperator U c * U a = U a * weightedOperator U c
  unfold weightedOperator
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← hU]
  apply Fintype.sum_equiv ((Equiv.mulLeft a⁻¹).trans (Equiv.mulRight a))
  intro g
  change c g • U (g * a) = c (a⁻¹ * g * a) • U (a * (a⁻¹ * g * a))
  rw [hc]
  congr 1
  group

omit [Fintype N] in
theorem weightedOperator_isHermitian (U : G → Matrix N N ℂ)
    (hU : ∀ g, (U g)ᴴ = U g⁻¹) (c : G → ℂ)
    (hc : ∀ g, star (c g) = c g⁻¹) :
    (weightedOperator U c).IsHermitian := by
  unfold Matrix.IsHermitian weightedOperator
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hU, hc]
  exact Equiv.sum_comp (Equiv.inv G) (fun g => c g • U g)

/-- A Hermitian convolution idempotent is a PSD projector. -/
theorem weightedOperator_posSemidef (U : G → Matrix N N ℂ)
    (hUmul : ∀ g h, U (g * h) = U g * U h)
    (hUstar : ∀ g, (U g)ᴴ = U g⁻¹) (c : G → ℂ)
    (hcstar : ∀ g, star (c g) = c g⁻¹)
    (hcconv : ∀ k, convolution c c k = c k) :
    (weightedOperator U c).PosSemidef := by
  have hh := weightedOperator_isHermitian U hUstar c hcstar
  have hi := weightedOperator_idempotent U hUmul c hcconv
  have hp := Matrix.posSemidef_conjTranspose_mul_self (weightedOperator U c)
  simpa only [hh.eq, hi] using hp

/-- The coefficient is written with `χ g`. For the conventional projector
formula using `χ (g⁻¹)`, pass that inverse character as the argument. For the
real symmetric-group characters in the bridge these expressions agree. -/
def characterCoefficient (χ : G → ℂ) (degree : ℕ) (g : G) : ℂ :=
  ((degree : ℂ) / (Fintype.card G : ℂ)) * χ g

def characterProjector (U : G → Matrix N N ℂ) (χ : G → ℂ)
    (degree : ℕ) : Matrix N N ℂ :=
  weightedOperator U (characterCoefficient χ degree)

/-- Explicit agreement with the conventional inverse-character formula for
an inversion-invariant character. This is the convention used for the
ordinary real symmetric-group characters in the bridge. -/
theorem characterProjector_eq_inverse_sum (U : G → Matrix N N ℂ)
    (χ : G → ℂ) (degree : ℕ) (hχinv : ∀ g, χ g⁻¹ = χ g) :
    characterProjector U χ degree =
      ((degree : ℂ) / (Fintype.card G : ℂ)) •
        ∑ g : G, χ g⁻¹ • U g := by
  simp only [characterProjector, weightedOperator, characterCoefficient,
    hχinv, Finset.smul_sum, MulAction.mul_smul]

theorem characterCoefficient_star (χ : G → ℂ) (degree : ℕ)
    (hχ : ∀ g, star (χ g) = χ g⁻¹) (g : G) :
    star (characterCoefficient χ degree g) =
      characterCoefficient χ degree g⁻¹ := by
  simp [characterCoefficient, hχ]

/-- This hypothesis is the ordinary character convolution theorem, not merely
pointwise character orthogonality. Its actual instantiation is deliberately
visible in the statement. -/
theorem characterCoefficient_convolution (χ : G → ℂ) (degree : ℕ)
    (hdegree : degree ≠ 0)
    (hχ : ∀ k : G, (∑ g : G, χ g * χ (g⁻¹ * k)) =
      ((Fintype.card G : ℂ) / (degree : ℂ)) * χ k) (k : G) :
    convolution (characterCoefficient χ degree) (characterCoefficient χ degree) k =
      characterCoefficient χ degree k := by
  have hd : (degree : ℂ) ≠ 0 := by exact_mod_cast hdegree
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold convolution characterCoefficient
  calc
    (∑ g : G,
      ((degree : ℂ) / (Fintype.card G : ℂ) * χ g) *
        ((degree : ℂ) / (Fintype.card G : ℂ) * χ (g⁻¹ * k))) =
        ((degree : ℂ) / (Fintype.card G : ℂ)) ^ 2 *
          ∑ g : G, χ g * χ (g⁻¹ * k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ = ((degree : ℂ) / (Fintype.card G : ℂ)) * χ k := by
      rw [hχ]
      field_simp
      ring

omit [Fintype N] in
theorem characterProjector_isHermitian (U : G → Matrix N N ℂ)
    (hUstar : ∀ g, (U g)ᴴ = U g⁻¹) (χ : G → ℂ) (degree : ℕ)
    (hχstar : ∀ g, star (χ g) = χ g⁻¹) :
    (characterProjector U χ degree).IsHermitian :=
  weightedOperator_isHermitian U hUstar _
    (characterCoefficient_star χ degree hχstar)

theorem characterProjector_commutes (U : G → Matrix N N ℂ)
    (hUmul : ∀ g h, U (g * h) = U g * U h) (χ : G → ℂ) (degree : ℕ)
    (hχclass : ∀ a g, χ (a⁻¹ * g * a) = χ g) (a : G) :
    Commute (characterProjector U χ degree) (U a) := by
  apply weightedOperator_commutes U hUmul
  intro b g
  simp only [characterCoefficient, hχclass]

theorem characterProjector_idempotent (U : G → Matrix N N ℂ)
    (hUmul : ∀ g h, U (g * h) = U g * U h) (χ : G → ℂ) (degree : ℕ)
    (hdegree : degree ≠ 0)
    (hχconv : ∀ k : G, (∑ g : G, χ g * χ (g⁻¹ * k)) =
      ((Fintype.card G : ℂ) / (degree : ℂ)) * χ k) :
    characterProjector U χ degree * characterProjector U χ degree =
      characterProjector U χ degree :=
  weightedOperator_idempotent U hUmul _
    (characterCoefficient_convolution χ degree hdegree hχconv)

theorem characterProjector_posSemidef (U : G → Matrix N N ℂ)
    (hUmul : ∀ g h, U (g * h) = U g * U h)
    (hUstar : ∀ g, (U g)ᴴ = U g⁻¹) (χ : G → ℂ) (degree : ℕ)
    (hdegree : degree ≠ 0)
    (hχstar : ∀ g, star (χ g) = χ g⁻¹)
    (hχconv : ∀ k : G, (∑ g : G, χ g * χ (g⁻¹ * k)) =
      ((Fintype.card G : ℂ) / (degree : ℂ)) * χ k) :
    (characterProjector U χ degree).PosSemidef :=
  weightedOperator_posSemidef U hUmul hUstar _
    (characterCoefficient_star χ degree hχstar)
    (characterCoefficient_convolution χ degree hdegree hχconv)

end

end Bridge.CharacterProjector
