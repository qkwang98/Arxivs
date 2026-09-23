# leftProjector dimension transport repaired; next exact blocker

The local construction of `leftProjector` now derives `hcard : d.card = a + b := hd.trans heq`, constructs a local matrix `P` with the required `Fin (a+b)` index by `rw [← hcard, hd]` followed by `exact tensorProjector (D := D) hd`, and applies the unchanged `localMatrix` and `regroupLeftMatrix` maps. Its signature and intended operator are unchanged; no global equivalence or helper was introduced.

The prefix through this definition compiles. Its axiom inventory is only `propext`, `Classical.choice`, and `Quot.sound`. All other Lean source files are unchanged, and cached dependencies were used without rebuilding infrastructure.

Full-file compilation reaches the next theorem, `leftProjector_hermitian`, and stops at its existing `subst heq` on line 103. No repair of that theorem was attempted, and positivity/bridge assembly has not been performed.

```text
Bridge/Young/TensorWitnessPositivity.lean:103:2: error: tactic 'subst' failed, invalid equality proof, it is not of the form (x = t) or (t = x)
  m + 1 = a + b
D : Type u_1
inst✝¹ : Fintype D
inst✝ : DecidableEq D
a b : ℕ
d : YoungDiagram
m : ℕ
hd : d.card = m + 1
heq : m + 1 = a + b
⊢ (leftProjector a b hd heq)ᴴ = leftProjector a b hd heq
```
