import Bridge.Young.WitnessShapes
import Bridge.Young.PrefixProjectorAlgebra

/-! The actual twenty witness operators in each verified Young representation.
All projectors are the genuine embedded character sums. Tail permutations are
literal permutations of the fourteen tensor positions. -/

noncomputable section
namespace LiebBridge.Young.WitnessOperators
open scoped Classical
open Certificate WitnessShapes PrefixProjector PrefixProjectorAlgebra

abbrev S14 := Equiv.Perm (Fin 14)

def swap12 : S14 := Equiv.swap 12 13

def swapPairs : S14 :=
  Equiv.swap 11 12 * Equiv.swap 10 11 * Equiv.swap 12 13 * Equiv.swap 11 12

variable (w : Witness) (hw : w ∈ rows) (p : Shape) (hp : IsPartition14 p)

abbrev Space := StandardTableau (partitionDiagram p hp) → ℂ

def rep : Representation ℂ S14 (Space p hp) :=
  ScalarExtension.representation ℂ (partitionDiagram_card p hp)

def etaP : Module.End ℂ (Space p hp) :=
  projector (m := 13 - 2*w.k) (eta := etaDiagram w hw)
    (by have := etaDiagram_card_add w hw; have := k_le_two w hw; omega)
    (partitionDiagram_card p hp) (by omega)

def muQ : Module.End ℂ (Space p hp) :=
  projector (m := 13 - w.k) (eta := muDiagram w hw)
    (by have := muDiagram_card_add w hw; have := k_le_two w hw; omega)
    (partitionDiagram_card p hp) (by omega)

def rightB : Module.End ℂ (Space p hp) :=
  if w.k = 2 then (1 / 2 : ℂ) • (1 + (w.sign : ℂ) • rep p hp swap12) else 1

def pairF : Module.End ℂ (Space p hp) :=
  rep p hp (if w.k = 1 then swap12 else swapPairs)

/-- The sandwich operator whose tensor realization is used by the direct
contraction theorem: Q B P F B Q, in this order. -/
def witness : Module.End ℂ (Space p hp) :=
  muQ w hw p hp * rightB w p hp * etaP w hw p hp * pairF w p hp *
    rightB w p hp * muQ w hw p hp

theorem etaP_idempotent : etaP w hw p hp * etaP w hw p hp = etaP w hw p hp :=
  projector_idempotent _ _ _

theorem muQ_idempotent : muQ w hw p hp * muQ w hw p hp = muQ w hw p hp :=
  projector_idempotent _ _ _

theorem etaP_commute_muQ : Commute (etaP w hw p hp) (muQ w hw p hp) :=
  projectors_commute _ _ _ _ _

theorem rep_swap12_square : rep p hp swap12 * rep p hp swap12 = 1 := by
  rw [← map_mul]
  simp [swap12]

include hw in
theorem rightB_idempotent : rightB w p hp * rightB w p hp = rightB w p hp := by
  unfold rightB
  split_ifs with hk
  · rcases (metadata w hw).sign_cases with hs | hs <;>
      simp only [hs, Rat.cast_one, Rat.cast_neg, one_smul, neg_smul]
    all_goals
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_add,
        one_mul, mul_one, neg_mul, mul_neg, neg_neg, rep_swap12_square]
      module
  · exact one_mul _

theorem muQ_commute_rightB : Commute (muQ w hw p hp) (rightB w p hp) := by
  unfold rightB
  split_ifs with hk
  · have hc := projector_commute_swap (eta := muDiagram w hw) (m := 13-w.k)
      (by have := muDiagram_card_add w hw; omega)
      (partitionDiagram_card p hp) (by omega) (12 : Fin 14) 13 (by change 13-w.k+1 ≤ 12; omega)
      (by change 13-w.k+1 ≤ 13; omega)
    change Commute (muQ w hw p hp) (rep p hp swap12) at hc
    change _ * _ = _ * _
    simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hc.eq]
  · exact Commute.one_right _

theorem etaP_commute_rightB : Commute (etaP w hw p hp) (rightB w p hp) := by
  unfold rightB
  split_ifs with hk
  · have hc := projector_commute_swap (eta := etaDiagram w hw) (m := 13-2*w.k)
      (by have := etaDiagram_card_add w hw; omega)
      (partitionDiagram_card p hp) (by omega) (12 : Fin 14) 13 (by change 13-2*w.k+1 ≤ 12; omega)
      (by change 13-2*w.k+1 ≤ 13; omega)
    change Commute (etaP w hw p hp) (rep p hp swap12) at hc
    change _ * _ = _ * _
    simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hc.eq]
  · exact Commute.one_right _

end LiebBridge.Young.WitnessOperators
