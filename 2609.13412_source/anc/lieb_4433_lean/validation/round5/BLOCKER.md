# Outside finite-sum localization repaired; next exact blocker

The only source change was adding `Matrix.sum_apply` to the existing entrywise `simp` proof of `outside_sum_localizes` in `TensorWitnessPositivity.lean`. Its single-permutation localization step was retained. No definitions, previously compiling files, representation/coefficient infrastructure, or earlier repairs were changed. Existing `.lake` dependencies were reused, with no clean or infrastructure rebuild.

The repaired declaration passes full-file elaboration. Compilation stops next at `left_sum_localizes`, line 58. This is the analogous finite-sum equality for the localized first-two-block operator. No repair to this next proof was attempted.

```text
Bridge/Young/TensorWitnessPositivity.lean:58:81: error: unsolved goals
case a
D : Type u_1
inst✝¹ : Fintype D
inst✝ : DecidableEq D
a b : ℕ
c : Equiv.Perm (Fin (a + b)) → ℂ
x y : Coordinates (Fin a) (Fin b) D
⊢ (∑ x, c x • Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (regroupLeftMatrix ((localMatrix a b) (tensorPermMatrix x))) 1)
      x y =
    (∑ x, c x • regroupLeftMatrix ((localMatrix a b) (tensorPermMatrix x))) x.1 y.1 * 1 x.2 y.2
```
