import Bridge.Young.YoungInequivalence
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# The actual Young representations as simple finite-dimensional representations

This module connects the proved simple group-algebra module to mathlib's categorical
`FDRep.Simple` interface, then applies ordinary character orthogonality to these actual
representations. No representation-label or orthogonality hypothesis is added.
-/

noncomputable section

namespace LiebBridge.Young.YoungFDRep

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Classical

private theorem simple_of_functor {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.Faithful] [F.ReflectsIsomorphisms]
    [F.PreservesMonomorphisms] [F.PreservesZeroMorphisms]
    (X : C) [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · intro hf hzero
      have hh : IsIso (F.map f) := inferInstance
      have hn := (Simple.mono_isIso_iff_nonzero (F.map f)).mp hh
      exact hn (by rw [hzero, F.map_zero])
    · intro hn
      have hn' : F.map f ≠ 0 := by
        intro hz
        apply hn
        apply F.map_injective
        simpa using hz
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr hn'
      exact isIso_of_reflects_iso f F

section Adapter

variable (K G : Type) [Field K] [Monoid G]

local instance forget_full : (forget₂ (FDRep K G) (Rep K G)).Full where
  map_surjective {X Y} f := ⟨FDRep.forget₂HomLinearEquiv X Y f, rfl⟩

local instance forget_preservesMono : (forget₂ (FDRep K G) (Rep K G)).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    haveI : Mono f.hom := by
      change Mono ((Action.forget (FGModuleCat K) G).map f)
      infer_instance
    haveI : Mono ((forget₂ (FGModuleCat K) (ModuleCat K)).map f.hom) := inferInstance
    apply (Rep.mono_iff_injective _).mpr
    exact (ModuleCat.mono_iff_injective ((forget₂ (FGModuleCat K) (ModuleCat K)).map f.hom)).mp
      inferInstance

/-- The standard bridge from a simple group-algebra module to a simple object of `FDRep`. -/
theorem simple_of_isSimpleModule {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : Representation K G V) [IsSimpleModule (MonoidAlgebra K G) ρ.asModule] :
    Simple (FDRep.of ρ) := by
  let E := Rep.equivalenceModuleMonoidAlgebra (k := K) (G := G)
  haveI : Simple (E.functor.obj (Rep.of ρ)) := by
    change Simple (ModuleCat.of (MonoidAlgebra K G) ρ.asModule)
    infer_instance
  haveI : Simple (Rep.of ρ) := simple_of_functor E.functor (Rep.of ρ)
  haveI : Simple ((forget₂ (FDRep K G) (Rep K G)).obj (FDRep.of ρ)) := by
    change Simple (Rep.of ρ)
    infer_instance
  exact simple_of_functor (forget₂ (FDRep K G) (Rep K G)) (FDRep.of ρ)

end Adapter

variable (K : Type) [Field K] [CharZero K]
variable {d eta nu : YoungDiagram} {n : ℕ}

/-- The genuine scalar-extended Young representation, bundled for the character API. -/
def representation (hcard : d.card = n+1) : FDRep K (Equiv.Perm (Fin (n+1))) :=
  FDRep.of (ScalarExtension.representation K hcard)

/-- Categorical simplicity of the actual Young representation. -/
theorem simple (hcard : d.card = n+1) :
    Simple (FDRep.of (ScalarExtension.representation K hcard)) := by
  letI := YoungIrreducibility.isSimpleModule K hcard
  exact simple_of_isSimpleModule K _ (ScalarExtension.representation K hcard)

instance representation_simple (hcard : d.card = n+1) : Simple (representation K hcard) :=
  simple K hcard

/-- The categorically bundled actual representations of distinct shapes are not isomorphic. -/
theorem not_nonempty_iso (hη : eta.card = n+1) (hν : nu.card = n+1) (hne : eta ≠ nu) :
    ¬ Nonempty (FDRep.of (ScalarExtension.representation K hη) ≅
      FDRep.of (ScalarExtension.representation K hν)) := by
  rintro ⟨e⟩
  apply YoungInequivalence.no_intertwining_linearEquiv K hη hν hne (FDRep.isoToLinearEquiv e)
  intro g x
  have hh := FDRep.Iso.conj_ρ e g
  have hx := congrArg (fun T : Module.End K (StandardTableau nu → K) =>
    T (FDRep.isoToLinearEquiv e x)) hh
  simpa [LinearEquiv.conj_apply] using hx.symm

theorem nonempty_iso_iff (hη : eta.card = n+1) (hν : nu.card = n+1) :
    Nonempty (FDRep.of (ScalarExtension.representation K hη) ≅
      FDRep.of (ScalarExtension.representation K hν)) ↔ eta = nu := by
  constructor
  · intro he
    by_contra hn
    exact not_nonempty_iso K hη hν hn he
  · intro he
    subst nu
    exact ⟨Iso.refl _⟩

/-- Ordinary character orthonormality for the actual constructed Young representations.
The right side is shape equality, discharged using the proved cross-shape inequivalence. -/
theorem char_orthonormal [IsAlgClosed K]
    (hη : eta.card = n+1) (hν : nu.card = n+1) :
    (Fintype.card (Equiv.Perm (Fin (n+1))) : K)⁻¹ *
        ∑ g : Equiv.Perm (Fin (n+1)),
          (FDRep.of (ScalarExtension.representation K hη)).character g *
            (FDRep.of (ScalarExtension.representation K hν)).character g⁻¹ =
      if eta = nu then 1 else 0 := by
  classical
  letI := simple K hη
  letI := simple K hν
  letI : Invertible (Fintype.card (Equiv.Perm (Fin (n+1))) : K) :=
    invertibleOfNonzero (by exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Equiv.Perm (Fin (n+1))) ≠ 0))
  have hh := FDRep.char_orthonormal
    (FDRep.of (ScalarExtension.representation K hη))
    (FDRep.of (ScalarExtension.representation K hν))
  simpa only [invOf_eq_inv, smul_eq_mul, nonempty_iso_iff, Nat.cast_one, Nat.cast_zero] using hh

end LiebBridge.Young.YoungFDRep
