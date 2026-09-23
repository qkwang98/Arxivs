# Local elaboration repair and next blocker

Only the proof of `TensorWitnessPositivity.tensorWitness_eq` was changed: its identity-matrix premise is now proved entrywise in the expected type. `tensorPermMatrix` and the completed representation/coefficient chain were not modified. Dependencies were loaded from existing `.lake` artifacts; no earlier infrastructure was rebuilt.

The full-file compilation passes this repaired declaration and next fails in `outside_sum_localizes` at line 48. No repair to that next proof was attempted.

The outstanding equality is linearity of `outsideLift` through the finite character-weighted sum, after taking matrix entries. This is a finite-sum elaboration/simplification obligation, not a new positivity or representation-theoretic assumption.

```text
Bridge/Young/TensorWitnessPositivity.lean:48:70: error: unsolved goals
case a
D : Type u_1
inst✝¹ : Fintype D
inst✝ : DecidableEq D
a b : ℕ
c : Equiv.Perm (Fin a) → ℂ
x y : Coordinates (Fin a) (Fin b) D
⊢ (∑ x,
        c x •
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (tensorPermMatrix x) 1)
            1)
      x y =
    (∑ g, c g • tensorPermMatrix g) x.1.1 y.1.1 * (1 x.1.2 y.1.2 * 1 x.2 y.2)
```
