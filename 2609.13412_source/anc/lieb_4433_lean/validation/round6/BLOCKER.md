# Left finite-sum localization repaired; first new blocker

The only source edit was adding `Matrix.sum_apply` to the existing entrywise proof of `left_sum_localizes`. The proof now checks. The prefix audit through `outside_prefixTensor` also compiles, and `#print axioms left_sum_localizes` reports only `propext`, `Classical.choice`, and `Quot.sound`. All definitions, earlier repairs, and completed infrastructure are unchanged. Cached `.lake` dependencies were reused.

Full-file compilation reaches the definition `leftProjector` and fails at `subst heq` on line 95. The hypothesis is `heq : m + 1 = a + b`, which is not an equality with a variable on either side, so `subst` cannot use it. No repair to this next blocker was attempted. The concrete positivity theorem and bridge have not been assembled.

```text
Bridge/Young/TensorWitnessPositivity.lean:95:2: error: tactic 'subst' failed, invalid equality proof, it is not of the form (x = t) or (t = x)
  m + 1 = a + b
D : Type u_1
inst✝¹ : Fintype D
inst✝ : DecidableEq D
a b : ℕ
d : YoungDiagram
m : ℕ
hd : d.card = m + 1
heq : m + 1 = a + b
⊢ Matrix ((Fin a → D) × (Fin b → D)) ((Fin a → D) × (Fin b → D)) ℂ
```
