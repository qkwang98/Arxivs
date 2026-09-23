# First integration blocker

TensorPairing.lean compiled after adding Matrix.sum_apply to the existing entrywise sum rewrite. No established compiling source changed; all 21 established files and all 54 checkpoint compiling Young files remain unchanged. Only TensorPairing.lean differs from the checkpoint. Cached dependencies were reused.

Stopped at the first error in TensorWitnessPositivity.tensorWitness_eq, line 40. This is a Lean elaboration/DecidableEq-instance mismatch for the identity matrix; the concrete positivity integration has not been completed. No fix was attempted after this error, as requested.

```text
error: ././././Bridge/Young/TensorWitnessPositivity.lean:40:70: application type mismatch
  matrixEvaluation_witnessCoeff tensorPermMatrix tensorPermMatrix_mul tensorPermMatrix_one
argument
  tensorPermMatrix_one
has type
  tensorPermMatrix 1 =
    @OfNat.ofNat (Matrix (Fin 14 → ?m.32266) (Fin 14 → ?m.32266) ℂ) 1
      (@One.toOfNat1 (Matrix (Fin 14 → ?m.32266) (Fin 14 → ?m.32266) ℂ)
        (@Matrix.one (Fin 14 → ?m.32266) ℂ (fun a b => Fintype.decidablePiFintype a b) Complex.instZero
          Complex.instOne)) : Prop
but is expected to have type
  tensorPermMatrix 1 =
    @OfNat.ofNat (Matrix (Fin 14 → D) (Fin 14 → D) ℂ) 1
      (@One.toOfNat1 (Matrix (Fin 14 → D) (Fin 14 → D) ℂ)
        (@Matrix.one (Fin 14 → D) ℂ (fun a b => Classical.propDecidable (a = b)) Complex.instZero
          Complex.instOne)) : Prop
```
