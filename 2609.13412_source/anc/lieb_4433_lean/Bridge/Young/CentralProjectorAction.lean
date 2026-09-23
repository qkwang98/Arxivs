import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-! Character central projectors on actual finite-dimensional simple modules.
Schur's lemma supplies scalar action, and character orthogonality fixes that
scalar. No projector-action identity is assumed. -/

noncomputable section
namespace LiebBridge.Young.CentralProjectorAction

open CategoryTheory
open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G]

def centralSum (V W : FDRep ℂ G) : Module.End ℂ W :=
  ∑ g : G, V.character (g⁻¹) • W.ρ g

theorem centralSum_commutes (V W : FDRep ℂ G) (h : G) :
    centralSum V W * W.ρ h = W.ρ h * centralSum V W := by
  unfold centralSum
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← map_mul]
  apply Fintype.sum_equiv ((Equiv.mulLeft h⁻¹).trans (Equiv.mulRight h))
  intro g
  change V.character g⁻¹ • W.ρ (g*h) =
    V.character ((h⁻¹*g*h)⁻¹) • W.ρ (h*(h⁻¹*g*h))
  have hchar : V.character ((h⁻¹*g*h)⁻¹) = V.character g⁻¹ := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using V.char_conj g⁻¹ h⁻¹
  rw [hchar]
  congr 2
  group

/-- A commuting endomorphism is scalar, by the proved categorical Schur lemma. -/
theorem scalar_of_commutes (W : FDRep ℂ G) [Simple W]
    (T : Module.End ℂ W) (hT : ∀ g, T * W.ρ g = W.ρ g * T) :
    ∃ c : ℂ, T = c • 1 := by
  let f : W ⟶ W :=
    { hom := ModuleCat.ofHom T
      comm := by
        intro g
        apply ModuleCat.hom_ext
        exact hT g }
  obtain ⟨c,hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  have hh := congrArg (fun p : W ⟶ W => p.hom.hom) hc
  exact hh.symm

def projector (V W : FDRep ℂ G) : Module.End ℂ W :=
  ((Module.finrank ℂ V : ℂ) / Fintype.card G) • centralSum V W

theorem projector_scalar (V W : FDRep ℂ G) [Simple W] :
    ∃ c : ℂ, projector V W = c • 1 := by
  apply scalar_of_commutes
  intro g
  unfold projector
  rw [smul_mul_assoc, mul_smul_comm, centralSum_commutes]

theorem centralSum_trace (V W : FDRep ℂ G) :
    LinearMap.trace ℂ W (centralSum V W) =
      ∑ g : G, V.character g⁻¹ * W.character g := by
  simp only [centralSum, map_sum, map_smul, smul_eq_mul, FDRep.character]

theorem projector_trace (V W : FDRep ℂ G) [Simple V] [Simple W] :
    LinearMap.trace ℂ W (projector V W) =
      (Module.finrank ℂ V : ℂ) * (if Nonempty (V ≅ W) then 1 else 0) := by
  classical
  letI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Fintype.card_ne_zero (α := G))
  have ho := FDRep.char_orthonormal W V
  simp only [invOf_eq_inv, smul_eq_mul, Iso.nonempty_iso_symm] at ho
  have hsum : (∑ g : G, V.character g⁻¹ * W.character g) =
      ∑ g : G, W.character g * V.character g⁻¹ := by
    apply Finset.sum_congr rfl
    intro g hg
    exact mul_comm _ _
  simp only [projector, map_smul, smul_eq_mul, centralSum_trace, hsum]
  rw [div_eq_mul_inv, mul_assoc, ho]

theorem finrank_ne_zero (W : FDRep ℂ G) [Simple W] : Module.finrank ℂ W ≠ 0 := by
  intro h
  haveI : Subsingleton W := (Module.finrank_zero_iff (R := ℂ) (M := W)).mp h
  apply CategoryTheory.id_nonzero W
  ext x
  exact @Subsingleton.elim W (inferInstanceAs (Subsingleton W)) _ _

/-- The character central projector selects a simple isomorphism class.
This is a theorem about the actual character sum, rather than an assumed
selector law. -/
theorem projector_eq (V W : FDRep ℂ G) [Simple V] [Simple W] :
    projector V W = if Nonempty (V ≅ W) then 1 else 0 := by
  classical
  obtain ⟨c,hc⟩ := projector_scalar V W
  have ht := projector_trace V W
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  have hw : (Module.finrank ℂ W : ℂ) ≠ 0 := by exact_mod_cast finrank_ne_zero W
  by_cases hiso : Nonempty (V ≅ W)
  · obtain ⟨e⟩ := hiso
    have hd : Module.finrank ℂ V = Module.finrank ℂ W :=
      (FDRep.isoToLinearEquiv e).finrank_eq
    rw [if_pos ⟨e⟩, mul_one, hd] at ht
    have hc1 : c = 1 := by apply (mul_right_cancel₀ hw); simpa using ht
    rw [hc, hc1, one_smul, if_pos ⟨e⟩]
  · rw [if_neg hiso, mul_zero] at ht
    have hc0 : c = 0 := (mul_eq_zero.mp ht).resolve_right hw
    rw [hc, hc0, zero_smul, if_neg hiso]

theorem projector_mul_trace (V W : FDRep ℂ G) (k : G) :
    LinearMap.trace ℂ W (projector V W * W.ρ k) =
      ((Module.finrank ℂ V : ℂ) / Fintype.card G) *
        ∑ g : G, V.character g⁻¹ * W.character (g*k) := by
  simp only [projector, centralSum, Finset.sum_mul, smul_mul_assoc,
    map_sum, map_smul, smul_eq_mul, ← map_mul, FDRep.character]

/-- The genuine shifted character convolution identity, derived by multiplying
the self-projector identity and taking its trace. Completeness of a list of
irreducibles is not an input to this theorem. -/
theorem character_convolution (V : FDRep ℂ G) [Simple V] (k : G) :
    (∑ g : G, V.character g * V.character (g⁻¹*k)) =
      ((Fintype.card G : ℂ) / Module.finrank ℂ V) * V.character k := by
  have hp : projector V V = 1 := by rw [projector_eq, if_pos ⟨Iso.refl V⟩]
  have ht := congrArg (fun T : Module.End ℂ V => LinearMap.trace ℂ V (T * V.ρ k)) hp
  change LinearMap.trace ℂ V (projector V V * V.ρ k) =
    LinearMap.trace ℂ V (1 * V.ρ k) at ht
  rw [projector_mul_trace, one_mul] at ht
  change ((Module.finrank ℂ V : ℂ) / Fintype.card G) *
    (∑ g : G, V.character g⁻¹ * V.character (g*k)) = V.character k at ht
  have hs : (∑ g : G, V.character g⁻¹ * V.character (g*k)) =
      ∑ g : G, V.character g * V.character (g⁻¹*k) := by
    apply Fintype.sum_equiv (Equiv.inv G)
    intro g
    simp
  rw [hs] at ht
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast finrank_ne_zero V
  have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := G)
  apply (mul_left_cancel₀ (div_ne_zero hd hg))
  rw [ht]
  field_simp
  ring

end LiebBridge.Young.CentralProjectorAction
