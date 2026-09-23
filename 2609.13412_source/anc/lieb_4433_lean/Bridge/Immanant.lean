import Bridge.TensorGram
import Mathlib.RepresentationTheory.Basic

/-!
Immanants associated to supplied character functions and their tensor operators.
The character function is an explicit argument. This file does not assert that
a function indexed by a partition is an irreducible symmetric-group character.
-/

open scoped BigOperators Matrix ComplexOrder

namespace LiebBridge
noncomputable section

variable {I D : Type*} [Fintype I] [Fintype D] [DecidableEq I]

/-- Generalized complex matrix function, in the usual permutation convention. -/
def complexImmanant (χ : Equiv.Perm I → ℂ) (A : Matrix I I ℂ) : ℂ :=
  ∑ σ : Equiv.Perm I, χ σ * ∏ i, A i (σ i)

/-- Complex permanent, before using Hermiticity to establish reality. -/
def complexPermanent (A : Matrix I I ℂ) : ℂ := complexImmanant (fun _ => 1) A

/-- Real part of the immanant. For Hermitian matrices and real characters
invariant under inversion, `complexImmanant_star` establishes reality. -/
def realImmanant (χ : Equiv.Perm I → ℝ) (A : Matrix I I ℂ) : ℝ :=
  (complexImmanant (fun σ => (χ σ : ℂ)) A).re

def permanent (A : Matrix I I ℂ) : ℝ := (complexPermanent A).re

/-- Tensor position permutations as complex linear maps. -/
def tensorPermLinear (σ : Equiv.Perm I) :
    Module.End ℂ (Tensor I D) where
  toFun := tensorPerm σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual symmetric-group representation on the coordinate tensor space. -/
def tensorRepresentation : Representation ℂ (Equiv.Perm I) (Tensor I D) where
  toFun := tensorPermLinear
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The character-weighted central-operator formula. Projector properties
require character-theoretic facts; they are not built into this definition. -/
def characterOperator (χ : Equiv.Perm I → ℂ) (degree : ℕ) :
    Module.End ℂ (Tensor I D) :=
  ((degree : ℂ) / Fintype.card (Equiv.Perm I)) •
    ∑ σ : Equiv.Perm I, χ (σ⁻¹) • tensorPermLinear σ

theorem tensorInner_smul_right (x y : Tensor I D) (a : ℂ) :
    tensorInner x (a • y) = a * tensorInner x y := by
  simp only [tensorInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem tensorInner_sum_right {J : Type*} [Fintype J]
    (x : Tensor I D) (y : J → Tensor I D) :
    tensorInner x (∑ j, y j) = ∑ j, tensorInner x (y j) := by
  simp only [tensorInner, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Exact factor `degree / |S_I|` in the Gram realization of the character
operator. No positivity, orthogonality, or irreducibility assumption occurs. -/
theorem characterOperator_gram_expectation (χ : Equiv.Perm I → ℂ) (degree : ℕ)
    (v : I → D → ℂ) :
    tensorInner (pureTensor v) (characterOperator χ degree (pureTensor v)) =
      ((degree : ℂ) / Fintype.card (Equiv.Perm I)) *
        complexImmanant χ (gramMatrix v) := by
  simp only [characterOperator, LinearMap.smul_apply, LinearMap.sum_apply,
    tensorInner_smul_right, tensorInner_sum_right, tensorPermLinear,
    LinearMap.coe_mk, AddHom.coe_mk, tensorInner_perm_pureTensor]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm I)) _ _ (fun σ => rfl)

/-- Hermitian Gram monomials are conjugated by inversion of the permutation. -/
theorem star_permutation_monomial (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (σ : Equiv.Perm I) :
    star (∏ i, A i (σ i)) = ∏ i, A i (σ⁻¹ i) := by
  classical
  have hentry (i j : I) : star (A i j) = A j i := by
    exact congrFun (congrFun hA j) i
  simp only [star_prod, hentry]
  simpa using Equiv.prod_comp σ (fun i => A i (σ⁻¹ i))

/-- Real inversion-invariant characters yield real immanants on all Hermitian
complex matrices, independently of positive semidefiniteness. -/
theorem complexImmanant_star (χ : Equiv.Perm I → ℝ)
    (hχ : ∀ σ, χ (σ⁻¹) = χ σ) (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    star (complexImmanant (fun σ => (χ σ : ℂ)) A) =
      complexImmanant (fun σ => (χ σ : ℂ)) A := by
  simp only [complexImmanant, star_sum, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  simp_rw [← Complex.star_def, star_permutation_monomial A hA]
  conv_lhs => arg 2; ext σ; rw [← hχ σ]
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm I)) _ _ (fun σ => mul_comm _ _)

end
end LiebBridge
