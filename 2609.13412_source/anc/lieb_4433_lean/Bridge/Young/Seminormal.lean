import Bridge.Young.TableauSwap
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The rational seminormal adjacent operators on genuine standard tableaux.
The off-diagonal term is present exactly when the swapped tableau is standard.
-/

namespace LiebBridge.Young
namespace StandardTableau

variable {d : YoungDiagram}

def rationalContent (t : StandardTableau d) (i : Fin d.card) : ℚ :=
  (boxContent (t.entry i).1 : ℤ)

def axial (t : StandardTableau d) (i j : Fin d.card) : ℚ :=
  t.rationalContent j - t.rationalContent i

theorem axial_ne_zero (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) : t.axial i j ≠ 0 := by
  have h := t.content_ne_of_label_distance_le_two (t.entry i) (t.entry j)
    (by simp only [number_entry]; omega) (by simp only [number_entry]; omega)
  have hi : (boxContent (t.entry j).1 : ℤ) - boxContent (t.entry i).1 ≠ 0 :=
    sub_ne_zero.mpr h.symm
  unfold axial rationalContent
  exact_mod_cast hi

theorem axial_of_forbidden (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : t.entry i ≤ t.entry j) :
    t.axial i j = 1 ∨ t.axial i j = -1 := by
  have h := t.content_gap_of_consecutive_comparable (t.entry i) (t.entry j)
    (by simpa only [number_entry] using hij) hs
  unfold axial rationalContent
  exact_mod_cast h

theorem adjacentSwap_allowed (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    ¬ (t.adjacentSwap i j hij).entry i ≤ (t.adjacentSwap i j hij).entry j := by
  rw [adjacentSwap_of_allowed _ _ _ _ hs]
  exact t.swapAllowed_swappable i j hij hs

theorem rationalContent_adjacentSwap (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) (k : Fin d.card) :
    (t.adjacentSwap i j hij).rationalContent k =
      t.rationalContent (Equiv.swap i j k) := by
  rw [adjacentSwap_of_allowed _ _ _ _ hs]
  rfl

theorem axial_adjacentSwap (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    (t.adjacentSwap i j hij).axial i j = -t.axial i j := by
  simp only [axial, rationalContent_adjacentSwap _ _ _ _ hs,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- Row form of the rational seminormal matrix. The source-column coefficient
at the other tableau is `1 + 1 / axial(source)`, hence `1 - 1 / axial(row)`. -/
def generator (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    Module.End ℚ (StandardTableau d → ℚ) where
  toFun v t := (t.axial i j)⁻¹ * v t +
    if ¬ t.entry i ≤ t.entry j then
      (1 - (t.axial i j)⁻¹) * v (t.adjacentSwap i j hij) else 0
  map_add' v w := by
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem generator_apply (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1)
    (v : StandardTableau d → ℚ) (t : StandardTableau d) :
    generator i j hij v t = (t.axial i j)⁻¹ * v t +
      if ¬ t.entry i ≤ t.entry j then
        (1 - (t.axial i j)⁻¹) * v (t.adjacentSwap i j hij) else 0 := rfl

/-- The actual tableau generator is an involution, including the diagonal-only
row and column cases. -/
theorem generator_square (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    generator i j hij * generator i j hij = 1 := by
  ext v t
  change generator i j hij (generator i j hij v) t = v t
  by_cases hs : ¬ t.entry i ≤ t.entry j
  · have hss := t.adjacentSwap_allowed i j hij hs
    have hd := t.axial_ne_zero i j hij
    simp only [generator_apply, if_pos hs, if_pos hss,
      axial_adjacentSwap _ _ _ _ hs, adjacentSwap_involutive i j hij t, inv_neg]
    field_simp
    ring
  · have hf := t.axial_of_forbidden i j hij (not_not.mp hs)
    simp only [generator_apply, if_neg hs, add_zero]
    rcases hf with hf | hf <;> rw [hf] <;> norm_num

theorem axial_disjoint_swap (t : StandardTableau d) (i j p q : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hpi : p ≠ i) (hpj : p ≠ j) (hqi : q ≠ i) (hqj : q ≠ j) :
    (t.adjacentSwap i j hij).axial p q = t.axial p q := by
  unfold axial rationalContent
  rw [adjacentSwap_entry_other _ _ _ _ _ hpi hpj,
    adjacentSwap_entry_other _ _ _ _ _ hqi hqj]

/-- Distant generators commute on the actual standard-tableau module. -/
theorem generator_commute (i j p q : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hpq : (q : ℕ) = (p : ℕ) + 1)
    (hpi : p ≠ i) (hpj : p ≠ j) (hqi : q ≠ i) (hqj : q ≠ j) :
    generator i j hij * generator p q hpq = generator p q hpq * generator i j hij := by
  ext v t
  change generator i j hij (generator p q hpq v) t =
    generator p q hpq (generator i j hij v) t
  simp only [generator_apply,
    axial_disjoint_swap _ _ _ _ _ _ hpi hpj hqi hqj,
    axial_disjoint_swap _ _ _ _ _ _ hpi.symm hqi.symm hpj.symm hqj.symm,
    adjacentSwap_entry_other _ _ _ _ _ hpi hpj,
    adjacentSwap_entry_other _ _ _ _ _ hqi hqj,
    adjacentSwap_entry_other _ _ _ _ _ hpi.symm hqi.symm,
    adjacentSwap_entry_other _ _ _ _ _ hpj.symm hqj.symm,
    adjacentSwap_commute _ _ _ _ _ _ _ hpi hpj hqi hqj]
  split_ifs <;> ring

/-- Diagonal multiplication by the content of a specified box label. -/
def contentOperator (i : Fin d.card) : Module.End ℚ (StandardTableau d → ℚ) where
  toFun v t := t.rationalContent i * v t
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' _ _ := by ext; simp [mul_left_comm]

private theorem local_content_identity (a b v w : ℚ) (h : b - a ≠ 0) :
    (b-a)⁻¹ * (a * ((b-a)⁻¹ * v + (1-(b-a)⁻¹) * w)) +
      (1-(b-a)⁻¹) * (b * (-(b-a)⁻¹ * w + (1+(b-a)⁻¹) * v)) +
      ((b-a)⁻¹ * v + (1-(b-a)⁻¹) * w) = b * v := by
  field_simp
  ring

/-- The Jucys--Murphy recurrence in the actual tableau operators. Once the
adjacent operators have been extended to `S_n`, this identifies the represented
Jucys--Murphy elements with the content diagonals. -/
theorem content_recurrence (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1) :
    generator i j hij * contentOperator i * generator i j hij + generator i j hij =
      contentOperator j := by
  ext v t
  change generator i j hij (contentOperator i (generator i j hij v)) t +
    generator i j hij v t = t.rationalContent j * v t
  by_cases hs : ¬ t.entry i ≤ t.entry j
  · have hss := t.adjacentSwap_allowed i j hij hs
    have hd := t.axial_ne_zero i j hij
    simp only [generator_apply, if_pos hs, if_pos hss, contentOperator,
      LinearMap.coe_mk, AddHom.coe_mk, rationalContent_adjacentSwap _ _ _ _ hs,
      Equiv.swap_apply_left, axial_adjacentSwap _ _ _ _ hs,
      adjacentSwap_involutive i j hij t, inv_neg]
    simpa only [axial, sub_neg_eq_add] using
      local_content_identity (t.rationalContent i) (t.rationalContent j)
        (v t) (v (t.adjacentSwap i j hij)) hd
  · have hf := t.axial_of_forbidden i j hij (not_not.mp hs)
    simp only [generator_apply, if_neg hs, add_zero, contentOperator,
      LinearMap.coe_mk, AddHom.coe_mk]
    rcases hf with hf | hf <;> rw [hf] <;> norm_num
    all_goals
      unfold axial at hf
      have hv := congrArg (fun x : ℚ => x * v t) hf
      simp only [sub_mul, one_mul, neg_one_mul] at hv
      linarith only [hv]

/-- The actual coordinate matrix, rather than an arbitrary list of numbers. -/
noncomputable def generatorMatrix (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    Matrix (StandardTableau d) (StandardTableau d) ℚ :=
  by classical exact LinearMap.toMatrix' (generator i j hij)

end StandardTableau
end LiebBridge.Young
