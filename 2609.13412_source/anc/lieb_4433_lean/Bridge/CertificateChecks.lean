import Bridge.CertificateData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace LiebBridge.Certificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem partitions14_length : partitions14.length = 135 := by decide +kernel

theorem witness01_computed :
    (partitions14.all fun nu => computedCoeff witness01 nu == storedCoeff witness01 nu) = true := by
  decide +kernel

theorem witness02_computed :
    (partitions14.all fun nu => computedCoeff witness02 nu == storedCoeff witness02 nu) = true := by
  decide +kernel

theorem witness03_computed :
    (partitions14.all fun nu => computedCoeff witness03 nu == storedCoeff witness03 nu) = true := by
  decide +kernel

theorem witness04_computed :
    (partitions14.all fun nu => computedCoeff witness04 nu == storedCoeff witness04 nu) = true := by
  decide +kernel

theorem witness05_computed :
    (partitions14.all fun nu => computedCoeff witness05 nu == storedCoeff witness05 nu) = true := by
  decide +kernel

theorem witness06_computed :
    (partitions14.all fun nu => computedCoeff witness06 nu == storedCoeff witness06 nu) = true := by
  decide +kernel

theorem witness07_computed :
    (partitions14.all fun nu => computedCoeff witness07 nu == storedCoeff witness07 nu) = true := by
  decide +kernel

theorem witness08_computed :
    (partitions14.all fun nu => computedCoeff witness08 nu == storedCoeff witness08 nu) = true := by
  decide +kernel

theorem witness09_computed :
    (partitions14.all fun nu => computedCoeff witness09 nu == storedCoeff witness09 nu) = true := by
  decide +kernel

theorem witness10_computed :
    (partitions14.all fun nu => computedCoeff witness10 nu == storedCoeff witness10 nu) = true := by
  decide +kernel

theorem witness11_computed :
    (partitions14.all fun nu => computedCoeff witness11 nu == storedCoeff witness11 nu) = true := by
  decide +kernel

theorem witness12_computed :
    (partitions14.all fun nu => computedCoeff witness12 nu == storedCoeff witness12 nu) = true := by
  decide +kernel

theorem witness13_computed :
    (partitions14.all fun nu => computedCoeff witness13 nu == storedCoeff witness13 nu) = true := by
  decide +kernel

theorem witness14_computed :
    (partitions14.all fun nu => computedCoeff witness14 nu == storedCoeff witness14 nu) = true := by
  decide +kernel

theorem witness15_computed :
    (partitions14.all fun nu => computedCoeff witness15 nu == storedCoeff witness15 nu) = true := by
  decide +kernel

theorem witness16_computed :
    (partitions14.all fun nu => computedCoeff witness16 nu == storedCoeff witness16 nu) = true := by
  decide +kernel

theorem witness17_computed :
    (partitions14.all fun nu => computedCoeff witness17 nu == storedCoeff witness17 nu) = true := by
  decide +kernel

theorem witness18_computed :
    (partitions14.all fun nu => computedCoeff witness18 nu == storedCoeff witness18 nu) = true := by
  decide +kernel

theorem witness19_computed :
    (partitions14.all fun nu => computedCoeff witness19 nu == storedCoeff witness19 nu) = true := by
  decide +kernel

theorem witness20_computed :
    (partitions14.all fun nu => computedCoeff witness20 nu == storedCoeff witness20 nu) = true := by
  decide +kernel

theorem rowsComputedCheck :
    (rows.all fun w => partitions14.all fun nu => computedCoeff w nu == storedCoeff w nu) = true := by
  simp only [rows, List.all_cons, List.all_nil, witness01_computed, witness02_computed, witness03_computed, witness04_computed, witness05_computed, witness06_computed, witness07_computed, witness08_computed, witness09_computed, witness10_computed, witness11_computed, witness12_computed, witness13_computed, witness14_computed, witness15_computed, witness16_computed, witness17_computed, witness18_computed, witness19_computed, witness20_computed, Bool.and_self]

theorem computedCoeff_eq_storedCoeff (w : Witness) (hw : w ∈ rows)
    (nu : Shape) (hnu : nu ∈ partitions14) : computedCoeff w nu = storedCoeff w nu := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp rowsComputedCheck w hw) nu hnu
  simpa using h

theorem weightsPositiveCheck : (rows.all fun w => decide (0 < w.weight)) = true := by
  decide +kernel

theorem weightsPositive (w : Witness) (hw : w ∈ rows) : 0 < w.weight := by
  exact of_decide_eq_true (List.all_eq_true.mp weightsPositiveCheck w hw)

theorem degree_4433 : hookDegree [4, 4, 3, 3] = 12012 := by decide +kernel
theorem degree_653 : hookDegree [6, 5, 3] = 15015 := by decide +kernel
theorem degree_644 : hookDegree [6, 4, 4] = 9009 := by decide +kernel
theorem degree_554 : hookDegree [5, 5, 4] = 6006 := by decide +kernel
theorem degree_5333 : hookDegree [5, 3, 3, 3] = 15015 := by decide +kernel

end LiebBridge.Certificate
