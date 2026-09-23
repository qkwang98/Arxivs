import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-!
# Separating diagonal operators and connected coefficient graphs

Finite products of normalized differences of separating diagonal operators recover every
coordinate projection. An invariant submodule is therefore spanned by coordinate vectors;
nonzero generator coefficients propagate these vectors along the coefficient graph.

All hypotheses in this module concern actual linear maps. No ordinary-character or
Young-representation identification is assumed or concluded.
-/

namespace LiebBridge.Young.DiagonalIrreducibility

open scoped BigOperators

variable {K B J : Type*} [Field K] [Fintype B] [DecidableEq B]

/-- A diagonal endomorphism of the finite coordinate module. -/
def diagonal (d : B → K) : Module.End K (B → K) where
  toFun x b := d b * x b
  map_add' x y := by funext b; exact mul_add _ _ _
  map_smul' a x := by funext b; simp [mul_left_comm, mul_assoc]

omit [Fintype B] [DecidableEq B] in
@[simp] theorem diagonal_apply (d : B → K) (x : B → K) (b : B) :
    diagonal d x b = d b * x b := rfl

/-- Projection onto one actual coordinate. -/
def coordinateProjection (b : B) : Module.End K (B → K) :=
  diagonal (fun a => if a = b then 1 else 0)

/-- The standard coordinate vector. -/
def basisVector (b : B) : B → K := Pi.single b 1

/-- Joint diagonal eigenvalue tuples distinguish every two different coordinate labels. -/
def Separates (c : J → B → K) : Prop :=
  ∀ a b, a ≠ b → ∃ i, c i a ≠ c i b

noncomputable def separatingIndex (c : J → B → K) (hc : Separates c)
    (t : B) (s : {s : B // s ≠ t}) : J :=
  Classical.choose (hc t s.val s.property.symm)

omit [Field K] [Fintype B] [DecidableEq B] in
theorem separatingIndex_ne (c : J → B → K) (hc : Separates c)
    (t : B) (s : {s : B // s ≠ t}) :
    c (separatingIndex c hc t s) t ≠ c (separatingIndex c hc t s) s.val :=
  Classical.choose_spec (hc t s.val s.property.symm)

/-- A normalized diagonal factor equal to one at `t` and zero at `s`. -/
noncomputable def filterFactor (c : J → B → K) (hc : Separates c)
    (t : B) (s : {s : B // s ≠ t}) (a : B) : K :=
  (c (separatingIndex c hc t s) t - c (separatingIndex c hc t s) s.val)⁻¹ *
    (c (separatingIndex c hc t s) a - c (separatingIndex c hc t s) s.val)

omit [Fintype B] [DecidableEq B] in
@[simp] theorem filterFactor_at_target (c : J → B → K) (hc : Separates c)
    (t : B) (s : {s : B // s ≠ t}) : filterFactor c hc t s t = 1 := by
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (separatingIndex_ne c hc t s))

omit [Fintype B] [DecidableEq B] in
@[simp] theorem filterFactor_at_excluded (c : J → B → K) (hc : Separates c)
    (t : B) (s : {s : B // s ≠ t}) : filterFactor c hc t s s.val = 0 := by
  simp [filterFactor]

/-- The finite interpolation product is exactly the coordinate indicator. -/
theorem product_filterFactor (c : J → B → K) (hc : Separates c) (t a : B) :
    (∏ s : {s : B // s ≠ t}, filterFactor c hc t s a) = if a = t then 1 else 0 := by
  by_cases ha : a = t
  · subst a
    simp
  · rw [if_neg ha]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨a,ha⟩ : {s : B // s ≠ t}))
      (filterFactor_at_excluded c hc t ⟨a,ha⟩)

/-- This explicitly expresses a coordinate projector as a product of the normalized factors. -/
theorem coordinateProjection_eq_product (c : J → B → K) (hc : Separates c) (t : B) :
    coordinateProjection t = diagonal
      (fun a => ∏ s : {s : B // s ≠ t}, filterFactor c hc t s a) := by
  apply LinearMap.ext
  intro x
  funext a
  simp only [coordinateProjection, diagonal_apply, product_filterFactor]

omit [Fintype B] [DecidableEq B] in
theorem filterFactor_invariant (W : Submodule K (B → K))
    (c : J → B → K) (hc : Separates c)
    (hW : ∀ i, W ∈ (diagonal (c i)).invtSubmodule)
    (t : B) (s : {s : B // s ≠ t}) :
    W ∈ (diagonal (filterFactor c hc t s)).invtSubmodule := by
  intro x hx
  change diagonal (filterFactor c hc t s) x ∈ W
  let i := separatingIndex c hc t s
  have hh : (c i t - c i s.val)⁻¹ • (diagonal (c i) x - c i s.val • x) ∈ W :=
    W.smul_mem _ (W.sub_mem (hW i hx) (W.smul_mem _ hx))
  convert hh using 1
  funext a
  simp only [diagonal_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, filterFactor]
  dsimp [i]
  ring

omit [Fintype B] [DecidableEq B] in
theorem diagonal_finset_product_invariant {S : Type*}
    (W : Submodule K (B → K)) (d : S → B → K) (F : Finset S)
    (hW : ∀ s ∈ F, W ∈ (diagonal (d s)).invtSubmodule) :
    W ∈ (diagonal (fun b => ∏ s ∈ F, d s b)).invtSubmodule := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro x hx
    simpa [diagonal] using hx
  | @insert s F hs ih =>
    have hF : W ∈ (diagonal (fun b => ∏ r ∈ F, d r b)).invtSubmodule :=
      ih (fun r hr => hW r (Finset.mem_insert_of_mem hr))
    have hsW := hW s (Finset.mem_insert_self s F)
    intro x hx
    change diagonal (fun b => ∏ r ∈ insert s F, d r b) x ∈ W
    have hh : diagonal (d s) (diagonal (fun b => ∏ r ∈ F, d r b) x) ∈ W := hsW (hF hx)
    convert hh using 1
    funext a
    simp [Finset.prod_insert hs, mul_assoc]

/-- Separating joint diagonal spectra force invariance under every coordinate projector. -/
theorem coordinateProjection_invariant (W : Submodule K (B → K))
    (c : J → B → K) (hc : Separates c)
    (hW : ∀ i, W ∈ (diagonal (c i)).invtSubmodule) (t : B) :
    W ∈ (coordinateProjection t).invtSubmodule := by
  rw [coordinateProjection_eq_product c hc t]
  exact diagonal_finset_product_invariant W (filterFactor c hc t) Finset.univ
    (fun s _ => filterFactor_invariant W c hc hW t s)

omit [Fintype B] in
theorem coordinateProjection_apply_single (b : B) (x : B → K) :
    coordinateProjection b x = Pi.single b (x b) := by
  funext a
  by_cases ha : a = b
  · subst a
    simp [coordinateProjection, Pi.single_apply]
  · simp [coordinateProjection, Pi.single_apply, ha, Ne.symm ha]

/-- A nonzero coordinate of a vector in an invariant submodule isolates its basis vector. -/
theorem basisVector_mem_of_nonzero_coordinate (W : Submodule K (B → K))
    (hW : ∀ b, W ∈ (coordinateProjection b).invtSubmodule)
    {x : B → K} (hx : x ∈ W) {b : B} (hb : x b ≠ 0) : basisVector (K := K) b ∈ W := by
  have hp : coordinateProjection b x ∈ W := hW b hx
  have hs := W.smul_mem (x b)⁻¹ hp
  convert hs using 1
  rw [coordinateProjection_apply_single]
  funext a
  by_cases ha : a = b <;>
    simp [basisVector, Pi.single_apply, ha, eq_comm, hb]

theorem eq_top_of_basisVector_mem (W : Submodule K (B → K))
    (hW : ∀ b, basisVector (K := K) b ∈ W) : W = ⊤ := by
  apply top_unique
  intro x hx
  rw [← Finset.univ_sum_single x]
  apply W.sum_mem
  intro b hb
  have hh := W.smul_mem (x b) (hW b)
  convert hh using 1
  funext a
  by_cases ha : a = b <;>
    simp [basisVector, Pi.single_apply, ha, eq_comm]

/-- A directed nonzero matrix coefficient, in the actual coordinate basis. -/
def CoefficientEdge {L : Type*} (T : L → Module.End K (B → K)) (a b : B) : Prop :=
  ∃ i, T i (basisVector (K := K) a) b ≠ 0

theorem basisVector_mem_of_edge {L : Type*} (W : Submodule K (B → K))
    (hW : ∀ b, W ∈ (coordinateProjection b).invtSubmodule)
    (T : L → Module.End K (B → K)) (hT : ∀ i, W ∈ (T i).invtSubmodule)
    {a b : B} (hab : CoefficientEdge T a b) (ha : basisVector (K := K) a ∈ W) :
    basisVector (K := K) b ∈ W := by
  obtain ⟨i,hi⟩ := hab
  exact basisVector_mem_of_nonzero_coordinate W hW (hT i ha) hi

/-- Coordinate invariance plus connected nonzero coefficients excludes proper submodules.
No sparsity assumption is needed: coordinate projections isolate the required coefficient. -/
theorem eq_bot_or_eq_top_of_connected_coefficients {L : Type*}
    (W : Submodule K (B → K))
    (hW : ∀ b, W ∈ (coordinateProjection b).invtSubmodule)
    (T : L → Module.End K (B → K)) (hT : ∀ i, W ∈ (T i).invtSubmodule)
    (hconnected : ∀ a b, Relation.ReflTransGen (CoefficientEdge T) a b) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff W).mp hbot
  have hnonzero : ∃ a, x a ≠ 0 := by
    by_contra! hh
    exact hx0 (funext hh)
  obtain ⟨a,ha⟩ := hnonzero
  have hbase := basisVector_mem_of_nonzero_coordinate W hW hx ha
  apply eq_top_of_basisVector_mem
  intro b
  have hp := hconnected a b
  induction hp with
  | refl => exact hbase
  | @tail b d hp hbd ih => exact basisVector_mem_of_edge W hW T hT hbd ih

/-- The main diagonal-spectrum and graph-connectivity irreducibility mechanism. -/
theorem eq_bot_or_eq_top_of_separating_diagonals {L : Type*}
    (W : Submodule K (B → K)) (c : J → B → K) (hc : Separates c)
    (hC : ∀ i, W ∈ (diagonal (c i)).invtSubmodule)
    (T : L → Module.End K (B → K)) (hT : ∀ i, W ∈ (T i).invtSubmodule)
    (hconnected : ∀ a b, Relation.ReflTransGen (CoefficientEdge T) a b) :
    W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_connected_coefficients W
    (coordinateProjection_invariant W c hc hC) T hT hconnected

/-- A graph-interface version suitable for adjacent-tableau swap graphs. -/
theorem eq_bot_or_eq_top_of_connected_relation {L : Type*}
    (W : Submodule K (B → K)) (c : J → B → K) (hc : Separates c)
    (hC : ∀ i, W ∈ (diagonal (c i)).invtSubmodule)
    (T : L → Module.End K (B → K)) (hT : ∀ i, W ∈ (T i).invtSubmodule)
    (R : B → B → Prop) (hedge : ∀ a b, R a b → CoefficientEdge T a b)
    (hconnected : ∀ a b, Relation.ReflTransGen R a b) : W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_separating_diagonals W c hc hC T hT
    (fun a b => (hconnected a b).mono (fun a b h => hedge a b h))

/-- The content-operator recurrence derives all diagonal invariance from adjacent invariance.
This avoids requiring a separate transposition-sum realization of the content operators. -/
theorem invariant_of_adjacent_recurrence {n : ℕ}
    (W : Submodule K (B → K))
    (D : Fin (n+1) → Module.End K (B → K))
    (S : Fin n → Module.End K (B → K))
    (hzero : D 0 = 0)
    (hrec : ∀ i, D i.succ = S i * D i.castSucc * S i + S i)
    (hS : ∀ i, W ∈ (S i).invtSubmodule) :
    ∀ i, W ∈ (D i).invtSubmodule := by
  intro i
  induction i using Fin.induction with
  | zero => rw [hzero]; simp
  | succ i ih =>
    intro x hx
    change D i.succ x ∈ W
    rw [hrec]
    exact W.add_mem (hS i (ih (hS i hx))) (hS i hx)

section Representation

variable {H L : Type*} [Monoid H]

/-- An invariant submodule is stable under every explicit group-algebra operator. -/
theorem diagonal_invariant_of_groupAlgebra
    (ρ : Representation K H (B → K))
    (W : Submodule K (B → K)) (hW : W ∈ ρ.invtSubmodule)
    (c : J → B → K) (q : J → MonoidAlgebra K H)
    (hq : ∀ i, ρ.asAlgebraHom (q i) = diagonal (c i)) :
    ∀ i, W ∈ (diagonal (c i)).invtSubmodule := by
  intro i x hx
  change diagonal (c i) x ∈ W
  rw [← hq]
  exact ρ.asAlgebraHom_mem_of_forall_mem W
    (fun g v hv => (ρ.mem_invtSubmodule.mp hW g) hv) x hx (q i)

/-- The representation-facing form with explicit diagonal elements of the group algebra. -/
theorem representation_invariant_eq_bot_or_eq_top
    (ρ : Representation K H (B → K))
    (c : J → B → K) (hc : Separates c)
    (q : J → MonoidAlgebra K H) (hq : ∀ i, ρ.asAlgebraHom (q i) = diagonal (c i))
    (g : L → H)
    (hconnected : ∀ a b, Relation.ReflTransGen (CoefficientEdge (fun i => ρ (g i))) a b)
    (W : Submodule K (B → K)) (hW : W ∈ ρ.invtSubmodule) : W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_separating_diagonals W c hc
    (diagonal_invariant_of_groupAlgebra ρ W hW c q hq)
    (fun i => ρ (g i)) (fun i => ρ.mem_invtSubmodule.mp hW (g i)) hconnected

/-- Standard mathlib simple-module output for a nonempty coordinate basis.
The diagonal realizations and coefficient connectivity remain explicit hypotheses. -/
theorem representation_isSimpleModule [Nonempty B]
    (ρ : Representation K H (B → K))
    (c : J → B → K) (hc : Separates c)
    (q : J → MonoidAlgebra K H) (hq : ∀ i, ρ.asAlgebraHom (q i) = diagonal (c i))
    (g : L → H)
    (hconnected : ∀ a b, Relation.ReflTransGen (CoefficientEdge (fun i => ρ (g i))) a b) :
    IsSimpleModule (MonoidAlgebra K H) ρ.asModule := by
  rw [IsSimpleModule, ← ρ.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun W => ?_⟩
  rcases representation_invariant_eq_bot_or_eq_top ρ c hc q hq g hconnected W.val W.property with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- Representation irreducibility using only the adjacent content recurrence. -/
theorem representation_invariant_eq_bot_or_eq_top_of_recurrence {n : ℕ}
    (ρ : Representation K H (B → K))
    (c : Fin (n+1) → B → K) (hc : Separates c) (g : Fin n → H)
    (hzero : diagonal (c 0) = 0)
    (hrec : ∀ i, diagonal (c i.succ) =
      ρ (g i) * diagonal (c i.castSucc) * ρ (g i) + ρ (g i))
    (hconnected : ∀ a b, Relation.ReflTransGen (CoefficientEdge (fun i => ρ (g i))) a b)
    (W : Submodule K (B → K)) (hW : W ∈ ρ.invtSubmodule) : W = ⊥ ∨ W = ⊤ := by
  have hS : ∀ i, W ∈ Module.End.invtSubmodule (ρ (g i)) := fun i => ρ.mem_invtSubmodule.mp hW (g i)
  exact eq_bot_or_eq_top_of_separating_diagonals W c hc
    (invariant_of_adjacent_recurrence W (fun i => diagonal (c i)) (fun i => ρ (g i)) hzero hrec hS)
    (fun i => ρ (g i)) hS hconnected

/-- Direct standard simple-module output from the adjacent content recurrence. -/
theorem representation_isSimpleModule_of_recurrence [Nonempty B] {n : ℕ}
    (ρ : Representation K H (B → K))
    (c : Fin (n+1) → B → K) (hc : Separates c) (g : Fin n → H)
    (hzero : diagonal (c 0) = 0)
    (hrec : ∀ i, diagonal (c i.succ) =
      ρ (g i) * diagonal (c i.castSucc) * ρ (g i) + ρ (g i))
    (hconnected : ∀ a b, Relation.ReflTransGen (CoefficientEdge (fun i => ρ (g i))) a b) :
    IsSimpleModule (MonoidAlgebra K H) ρ.asModule := by
  rw [IsSimpleModule, ← ρ.mapSubmodule.isSimpleOrder_iff]
  refine ⟨fun W => ?_⟩
  rcases representation_invariant_eq_bot_or_eq_top_of_recurrence
      ρ c hc g hzero hrec hconnected W.val W.property with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end Representation

end LiebBridge.Young.DiagonalIrreducibility
