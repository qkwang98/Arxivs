import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Positivity

/-!
# Central averaging and real character expansion

This file proves a finite-group algebra lemma. Orthogonality, conjugation
invariance, and spanning of the supplied real character functions are explicit
hypotheses. In particular, this module neither postulates the bridge identity
nor identifies any finite tableau matrices with symmetric-group irreducibles.
-/

namespace Bridge.CentralAveraging

open scoped BigOperators
noncomputable section

variable {G : Type*} [Group G] [Fintype G]

def IsClassFunction (f : G → ℝ) : Prop :=
  ∀ a g, f (a⁻¹ * g * a) = f g

def centralCoefficient (w : G → ℝ) (g : G) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ a : G, w (a⁻¹ * g * a)

def pairing (w m : G → ℝ) : ℝ := ∑ g : G, w g * m g

private def conjugationEquiv (a : G) : G ≃ G :=
  (Equiv.mulLeft a⁻¹).trans (Equiv.mulRight a)

omit [Fintype G] in
@[simp] private theorem conjugationEquiv_apply (a g : G) :
    conjugationEquiv a g = a⁻¹ * g * a := rfl

theorem centralCoefficient_isClassFunction (w : G → ℝ) :
    IsClassFunction (centralCoefficient w) := by
  intro a g
  unfold centralCoefficient
  congr 1
  calc
    (∑ b : G, w (b⁻¹ * (a⁻¹ * g * a) * b)) =
        ∑ b : G, w ((a * b)⁻¹ * g * (a * b)) := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      group
    _ = ∑ b : G, w (b⁻¹ * g * b) :=
      Equiv.sum_comp (Equiv.mulLeft a) (fun b => w (b⁻¹ * g * b))

theorem pairing_centralCoefficient_classFunction (w χ : G → ℝ)
    (hχ : IsClassFunction χ) :
    pairing (centralCoefficient w) χ = pairing w χ := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hconj (a : G) :
      (∑ g : G, w (a⁻¹ * g * a) * χ g) = ∑ g : G, w g * χ g := by
    calc
      (∑ g : G, w (a⁻¹ * g * a) * χ g) =
          ∑ g : G, w (conjugationEquiv a g) * χ (conjugationEquiv a g) := by
        apply Finset.sum_congr rfl
        intro g hg
        simp only [conjugationEquiv_apply, hχ a g]
      _ = ∑ g : G, w g * χ g :=
        Equiv.sum_comp (conjugationEquiv a) (fun g => w g * χ g)
  unfold pairing centralCoefficient
  simp only [mul_assoc] at hconj
  simp only [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hconj]
  simp [hcard]

theorem pairing_centralCoefficient_eq_conjugate_average (w m : G → ℝ) :
    pairing (centralCoefficient w) m =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ a : G, pairing w (fun g => m (a * g * a⁻¹)) := by
  have hconj (a : G) :
      (∑ g : G, w (a⁻¹ * g * a) * m g) =
        ∑ g : G, w g * m (a * g * a⁻¹) := by
    apply Fintype.sum_equiv (conjugationEquiv a)
    intro g
    simp only [conjugationEquiv_apply]
    congr 1
    congr 1
    group
  unfold pairing centralCoefficient
  simp only [mul_assoc] at hconj
  simp only [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hconj]

/-- Positivity survives central averaging whenever every conjugated test
function has nonnegative pairing with the original coefficient function. -/
theorem pairing_centralCoefficient_nonneg (w m : G → ℝ)
    (h : ∀ a : G, 0 ≤ pairing w (fun g => m (a * g * a⁻¹))) :
    0 ≤ pairing (centralCoefficient w) m := by
  rw [pairing_centralCoefficient_eq_conjugate_average]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun a ha => h a))

section CharacterExpansion

variable {P : Type*} [Fintype P] [DecidableEq P]

def CharacterOrthogonal (χ : P → G → ℝ) : Prop :=
  ∀ i j, (∑ g : G, χ i g * χ j g) =
    if i = j then (Fintype.card G : ℝ) else 0

def ClassFunctionSpan (χ : P → G → ℝ) : Prop :=
  ∀ f : G → ℝ, IsClassFunction f →
    ∃ c : P → ℝ, ∀ g, f g = ∑ i : P, c i * χ i g

/-- Fourier reconstruction on the span of an orthogonal character family. -/
theorem reconstruction_of_span (χ : P → G → ℝ)
    (horth : CharacterOrthogonal χ) (f : G → ℝ)
    (hspan : ∃ c : P → ℝ, ∀ g, f g = ∑ i : P, c i * χ i g) (g : G) :
    f g = (Fintype.card G : ℝ)⁻¹ *
      ∑ i : P, pairing f (χ i) * χ i g := by
  obtain ⟨c, hc⟩ := hspan
  unfold CharacterOrthogonal at horth
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hcoeff (i : P) : pairing f (χ i) = (Fintype.card G : ℝ) * c i := by
    unfold pairing
    simp_rw [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, horth]
    simp [mul_comm]
  simp_rw [hcoeff, mul_assoc]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul, hc]

/-- Centralization expands with coefficients equal to the original character
pairings, not the pairings of an unrelated or assumed central element. -/
theorem centralCoefficient_character_expansion (χ : P → G → ℝ)
    (hclass : ∀ i, IsClassFunction (χ i))
    (horth : CharacterOrthogonal χ) (hspan : ClassFunctionSpan χ)
    (w : G → ℝ) (g : G) :
    centralCoefficient w g = (Fintype.card G : ℝ)⁻¹ *
      ∑ i : P, pairing w (χ i) * χ i g := by
  have hf := hspan (centralCoefficient w) (centralCoefficient_isClassFunction w)
  rw [reconstruction_of_span χ horth _ hf]
  simp_rw [pairing_centralCoefficient_classFunction w _ (hclass _)]

theorem pairing_centralCoefficient_character_expansion (χ : P → G → ℝ)
    (hclass : ∀ i, IsClassFunction (χ i))
    (horth : CharacterOrthogonal χ) (hspan : ClassFunctionSpan χ)
    (w m : G → ℝ) :
    pairing (centralCoefficient w) m = (Fintype.card G : ℝ)⁻¹ *
      ∑ i : P, pairing w (χ i) * pairing (χ i) m := by
  unfold pairing
  simp only [centralCoefficient_character_expansion χ hclass horth hspan,
    mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [pairing, ← Finset.mul_sum]
  simp only [Finset.sum_mul, mul_assoc]

/-- The character-weighted form obtained from any conjugate-positive
coefficient function is nonnegative. The character assumptions must be
instantiated separately for ordinary symmetric-group irreducibles. -/
theorem character_weighted_pairings_nonneg (χ : P → G → ℝ)
    (hclass : ∀ i, IsClassFunction (χ i))
    (horth : CharacterOrthogonal χ) (hspan : ClassFunctionSpan χ)
    (w m : G → ℝ)
    (hpositive : ∀ a : G, 0 ≤ pairing w (fun g => m (a * g * a⁻¹))) :
    0 ≤ ∑ i : P, pairing w (χ i) * pairing (χ i) m := by
  have h := pairing_centralCoefficient_nonneg w m hpositive
  rw [pairing_centralCoefficient_character_expansion χ hclass horth hspan] at h
  exact nonneg_of_mul_nonneg_right h (by positivity)

end CharacterExpansion

end

end Bridge.CentralAveraging
