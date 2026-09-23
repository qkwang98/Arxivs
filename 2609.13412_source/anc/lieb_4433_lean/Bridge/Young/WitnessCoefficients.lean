import Bridge.Young.RealCoefficientAlgebra
import Bridge.Young.WitnessOperators
import Bridge.Young.YoungCharacterCompleteness

/-! The real group-algebra coefficients of the concrete witness `Q B P F B Q`.
All evaluations use the actual embedded prefix character sums and literal tail
permutations. The same coefficients can be evaluated in Young or tensor modules. -/

noncomputable section
namespace LiebBridge.Young.WitnessCoefficients
open scoped BigOperators Classical
open Certificate WitnessShapes RealCoefficientAlgebra PrefixRepresentation
open WitnessOperators

def prefixCoeff {d : YoungDiagram} {m : ℕ} (hd : d.card = m+1) (hm : m+1 ≤ 14) :
    S14 → ℝ :=
  pushforward (prefixEmbedding hm) (fun g =>
    ((YoungProjectors.degree d : ℝ) / Fintype.card (Equiv.Perm (Fin (m+1)))) *
      YoungCharacter.realCharacter hd g⁻¹)

variable {N : Type*} [Fintype N]

theorem matrixEvaluation_prefixCoeff {d : YoungDiagram} {m : ℕ}
    (hd : d.card = m+1) (hm : m+1 ≤ 14) (U : S14 → Matrix N N ℂ) :
    matrixEvaluation U (prefixCoeff hd hm) =
      ((YoungProjectors.degree d : ℂ) / Fintype.card (Equiv.Perm (Fin (m+1)))) •
        ∑ g : Equiv.Perm (Fin (m+1)), YoungProjectors.character hd g⁻¹ •
          U (prefixEmbedding hm g) := by
  rw [prefixCoeff, matrixEvaluation_pushforward]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    ← YoungCharacter.complex_character_eq_real, YoungProjectors.character,
    Finset.smul_sum, mul_smul]

def etaCoeff (w : Witness) (hw : w ∈ rows) : S14 → ℝ :=
  prefixCoeff (m := 13-2*w.k) (d := etaDiagram w hw)
    (by have := etaDiagram_card_add w hw; have := k_le_two w hw; omega) (by omega)

def muCoeff (w : Witness) (hw : w ∈ rows) : S14 → ℝ :=
  prefixCoeff (m := 13-w.k) (d := muDiagram w hw)
    (by have := muDiagram_card_add w hw; have := k_le_two w hw; omega) (by omega)

def bCoeff (w : Witness) : S14 → ℝ :=
  if w.k = 2 then (1/2 : ℝ) • (delta 1 + (w.sign : ℝ) • delta swap12) else delta 1

def fCoeff (w : Witness) : S14 → ℝ :=
  delta (if w.k = 1 then swap12 else swapPairs)

def witnessCoeff (w : Witness) (hw : w ∈ rows) : S14 → ℝ :=
  realConvolution
    (realConvolution
      (realConvolution
        (realConvolution (realConvolution (muCoeff w hw) (bCoeff w)) (etaCoeff w hw))
        (fCoeff w))
      (bCoeff w))
    (muCoeff w hw)

def matrixB (U : S14 → Matrix N N ℂ) (w : Witness) : Matrix N N ℂ :=
  if w.k = 2 then (1/2 : ℂ) • (1 + (w.sign : ℂ) • U swap12) else 1

theorem matrixEvaluation_bCoeff (U : S14 → Matrix N N ℂ) (h1 : U 1 = 1)
    (w : Witness) : matrixEvaluation U (bCoeff w) = matrixB U w := by
  unfold bCoeff matrixB
  split_ifs <;> simp only [matrixEvaluation_smul, matrixEvaluation_add,
    matrixEvaluation_delta, h1, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_ratCast]

theorem matrixEvaluation_witnessCoeff (U : S14 → Matrix N N ℂ)
    (hU : ∀ g h, U (g*h) = U g * U h) (h1 : U 1 = 1)
    (w : Witness) (hw : w ∈ rows) :
    matrixEvaluation U (witnessCoeff w hw) =
      matrixEvaluation U (muCoeff w hw) * matrixB U w *
        matrixEvaluation U (etaCoeff w hw) *
        U (if w.k = 1 then swap12 else swapPairs) *
        matrixB U w * matrixEvaluation U (muCoeff w hw) := by
  simp only [witnessCoeff, matrixEvaluation_convolution U hU,
    matrixEvaluation_bCoeff U h1, fCoeff, matrixEvaluation_delta]

section YoungEvaluation
variable (w : Witness) (hw : w ∈ rows) (p : Shape) (hp : IsPartition14 p)

theorem endEvaluation_prefixCoeff {d : YoungDiagram} {m : ℕ}
    (hd : d.card = m+1) (hm : m+1 ≤ 14) :
    endEvaluation (rep p hp) (prefixCoeff hd hm) =
      PrefixProjector.projector hd (partitionDiagram_card p hp) hm := by
  rw [prefixCoeff, endEvaluation_pushforward]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    ← YoungCharacter.complex_character_eq_real, YoungProjectors.character,
    PrefixProjector.projector, Finset.smul_sum, mul_smul, rep]

theorem endEvaluation_etaCoeff :
    endEvaluation (rep p hp) (etaCoeff w hw) = etaP w hw p hp :=
  endEvaluation_prefixCoeff p hp _ _

theorem endEvaluation_muCoeff :
    endEvaluation (rep p hp) (muCoeff w hw) = muQ w hw p hp :=
  endEvaluation_prefixCoeff p hp _ _

theorem endEvaluation_bCoeff :
    endEvaluation (rep p hp) (bCoeff w) = rightB w p hp := by
  unfold bCoeff rightB
  split_ifs <;> simp only [endEvaluation_smul, endEvaluation_add, endEvaluation_delta,
    map_one, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_ratCast]

theorem endEvaluation_fCoeff :
    endEvaluation (rep p hp) (fCoeff w) = pairF w p hp :=
  endEvaluation_delta _ _

/-- Exact identification of the coefficient evaluation with the parent's
actual Young witness operator, preserving all six factors and their order. -/
theorem endEvaluation_witnessCoeff :
    endEvaluation (rep p hp) (witnessCoeff w hw) = witness w hw p hp := by
  simp only [witnessCoeff, endEvaluation_convolution _ (fun g h => map_mul _ g h),
    endEvaluation_muCoeff, endEvaluation_bCoeff, endEvaluation_etaCoeff,
    endEvaluation_fCoeff, witness]

/-- The coefficient-character pairing equals the actual witness trace.
No numerical value of this trace or character degree is assumed. -/
theorem trace_witness_eq_pairing :
    LinearMap.trace ℂ (Space p hp) (witness w hw p hp) =
      (Bridge.CentralAveraging.pairing (witnessCoeff w hw)
        (YoungCharacterCompleteness.character14 ⟨p,hp⟩) : ℂ) := by
  rw [← endEvaluation_witnessCoeff]
  simp only [endEvaluation, map_sum, map_smul, smul_eq_mul,
    Bridge.CentralAveraging.pairing, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  exact YoungCharacter.complex_character_eq_real (partitionDiagram_card p hp) g

end YoungEvaluation
end LiebBridge.Young.WitnessCoefficients
