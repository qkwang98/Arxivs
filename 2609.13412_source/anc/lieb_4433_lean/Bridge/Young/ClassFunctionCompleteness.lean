import Bridge.CentralAveraging
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! An orthogonal family of class functions spans as soon as its size is at
least the number of conjugacy classes. This is a dimension argument on the
actual quotient by conjugacy, with no completeness hypothesis. -/

noncomputable section
namespace LiebBridge.Young.ClassFunctionCompleteness
open scoped BigOperators
open Bridge.CentralAveraging

variable {G P : Type*} [Group G] [Fintype G] [Fintype P] [DecidableEq P]

def descend (f : G → ℝ) (hf : IsClassFunction f) : ConjClasses G → ℝ :=
  Quotient.lift f (by
    intro g h hconj
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    subst h
    simpa only [inv_inv] using (hf a⁻¹ g).symm)

omit [Fintype G] in
@[simp]
theorem descend_mk (f : G → ℝ) (hf : IsClassFunction f) (g : G) :
    descend f hf (ConjClasses.mk g) = f g := rfl

theorem descended_linearIndependent (χ : P → G → ℝ)
    (hclass : ∀ p, IsClassFunction (χ p)) (horth : CharacterOrthogonal χ) :
    LinearIndependent ℝ (fun p => descend (χ p) (hclass p)) := by
  classical
  unfold CharacterOrthogonal at horth
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hzero (g : G) : ∑ p : P, c p * χ p g = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, descend_mk, Pi.zero_apply]
      using congrFun hc (ConjClasses.mk g)
  have hz : (Fintype.card G : ℝ) * c j = 0 := by
    calc
      (Fintype.card G : ℝ) * c j =
          ∑ p : P, c p * ∑ g : G, χ p g * χ j g := by
        simp only [horth]
        simp [mul_comm]
      _ = ∑ g : G, (∑ p : P, c p * χ p g) * χ j g := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp only [hzero, zero_mul, Finset.sum_const_zero]
  exact (mul_eq_zero.mp hz).resolve_left (by positivity)

theorem classFunctionSpan_of_card_le [Fintype (ConjClasses G)]
    (χ : P → G → ℝ) (hclass : ∀ p, IsClassFunction (χ p))
    (horth : CharacterOrthogonal χ)
    (hcard : Fintype.card (ConjClasses G) ≤ Fintype.card P) : ClassFunctionSpan χ := by
  classical
  let v : P → ConjClasses G → ℝ := fun p => descend (χ p) (hclass p)
  have hli : LinearIndependent ℝ v := descended_linearIndependent χ hclass horth
  have hdim : Fintype.card P = Module.finrank ℝ (ConjClasses G → ℝ) := by
    apply Nat.le_antisymm hli.fintype_card_le_finrank
    simpa only [Module.finrank_fintype_fun_eq_card] using hcard
  let b : Basis P ℝ (ConjClasses G → ℝ) :=
    Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hdim).ge
  intro f hf
  refine ⟨fun p => b.repr (descend f hf) p, ?_⟩
  intro g
  have he := congrFun (b.sum_repr (descend f hf)) (ConjClasses.mk g)
  simpa only [b, Basis.coe_mk, v, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, descend_mk] using he.symm

end LiebBridge.Young.ClassFunctionCompleteness
