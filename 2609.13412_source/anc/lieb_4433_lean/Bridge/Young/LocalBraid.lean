import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The universal rational seminormal braid calculation on all six orders of
three pairwise distinct contents. This ambient calculation does not assert that
an arbitrary truncation to standard tableaux preserves the braid relation. -/

namespace LiebBridge.Young.LocalBraid
open scoped Matrix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Orbit order: `abc, bac, acb, cab, bca, cba`. -/
def orders (a b c : ℚ) : Fin 6 → Fin 3 → ℚ :=
  ![![a, b, c], ![b, a, c], ![a, c, b], ![c, a, b], ![b, c, a], ![c, b, a]]

def swap1 : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]
def swap2 : Fin 6 → Fin 6 := ![2, 4, 0, 5, 1, 3]

def gap1 (a b c : ℚ) : Fin 6 → ℚ := ![b-a, a-b, c-a, a-c, c-b, b-c]
def gap2 (a b c : ℚ) : Fin 6 → ℚ := ![c-b, c-a, b-c, b-a, a-c, a-b]

/-- Matrix entries are indexed by target row and source column. -/
def adjacentMatrix (swap : Fin 6 → Fin 6) (gap : Fin 6 → ℚ) :
    Matrix (Fin 6) (Fin 6) ℚ := fun target source =>
  (if target = source then 1 / gap source else 0) +
    (if target = swap source then 1 + 1 / gap source else 0)

def s1 (a b c : ℚ) : Matrix (Fin 6) (Fin 6) ℚ := adjacentMatrix swap1 (gap1 a b c)
def s2 (a b c : ℚ) : Matrix (Fin 6) (Fin 6) ℚ := adjacentMatrix swap2 (gap2 a b c)

theorem gap1_eq (a b c : ℚ) (i : Fin 6) :
    gap1 a b c i = orders a b c i 1 - orders a b c i 0 := by
  fin_cases i <;> rfl

theorem gap2_eq (a b c : ℚ) (i : Fin 6) :
    gap2 a b c i = orders a b c i 2 - orders a b c i 1 := by
  fin_cases i <;> rfl

theorem orders_swap1 (a b c : ℚ) (i : Fin 6) :
    orders a b c (swap1 i) =
      ![orders a b c i 1, orders a b c i 0, orders a b c i 2] := by
  fin_cases i <;> rfl

theorem orders_swap2 (a b c : ℚ) (i : Fin 6) :
    orders a b c (swap2 i) =
      ![orders a b c i 0, orders a b c i 2, orders a b c i 1] := by
  fin_cases i <;> rfl

theorem s1_sq (a b c : ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    s1 a b c * s1 a b c = 1 := by
  have hab' := sub_ne_zero.mpr hab
  have hba' := sub_ne_zero.mpr hab.symm
  have hac' := sub_ne_zero.mpr hac
  have hca' := sub_ne_zero.mpr hac.symm
  have hbc' := sub_ne_zero.mpr hbc
  have hcb' := sub_ne_zero.mpr hbc.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1, adjacentMatrix, swap1, gap1, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem s2_sq (a b c : ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    s2 a b c * s2 a b c = 1 := by
  have hab' := sub_ne_zero.mpr hab
  have hba' := sub_ne_zero.mpr hab.symm
  have hac' := sub_ne_zero.mpr hac
  have hca' := sub_ne_zero.mpr hac.symm
  have hbc' := sub_ne_zero.mpr hbc
  have hcb' := sub_ne_zero.mpr hbc.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s2, adjacentMatrix, swap2, gap2, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem braid (a b c : ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    s1 a b c * s2 a b c * s1 a b c = s2 a b c * s1 a b c * s2 a b c := by
  have hab' := sub_ne_zero.mpr hab
  have hba' := sub_ne_zero.mpr hab.symm
  have hac' := sub_ne_zero.mpr hac
  have hca' := sub_ne_zero.mpr hac.symm
  have hbc' := sub_ne_zero.mpr hbc
  have hcb' := sub_ne_zero.mpr hbc.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1, s2, adjacentMatrix, swap1, swap2, gap1, gap2,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> simp

end LiebBridge.Young.LocalBraid
