import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic

/-! The cyclic reduction in the independent audit. No swap is commuted past
the intermediate projector. The only commutation used is between the two
projectors with disjoint supports. -/

namespace LiebBridge.Young.WitnessTraceReduction

open scoped Matrix Kronecker

variable {K N : Type*} [CommRing K] [Fintype N]

theorem sandwich_trace (P Q B F : Matrix N N K)
    (hQ : Q*Q = Q) (hB : B*B = B) (hBQ : B*Q = Q*B) :
    Matrix.trace (Q*B*P*F*B*Q) = Matrix.trace (Q*B*P*F) := by
  calc
    Matrix.trace (Q*B*P*F*B*Q) = Matrix.trace ((Q*B*P*F)*(B*Q)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((B*Q)*(Q*B*P*F)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B*(Q*Q)*B*P*F) := by congr 1; noncomm_ring
    _ = Matrix.trace (B*Q*B*P*F) := by rw [hQ]
    _ = Matrix.trace (Q*(B*B)*P*F) := by rw [hBQ]; congr 1; noncomm_ring
    _ = Matrix.trace (Q*B*P*F) := by rw [hB]

/-- The prefix multiplicity is the actual size of the inner tableau basis. -/
theorem trace_identity_tensor {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix N N K) :
    Matrix.trace ((1 : Matrix I I K) ⊗ₖ M) =
      (Fintype.card I : K) * Matrix.trace M := by
  rw [Matrix.trace_kronecker, Matrix.trace_one]

end LiebBridge.Young.WitnessTraceReduction
