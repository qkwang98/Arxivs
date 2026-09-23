# Final Lean validation summary

A separate final validation was run after the earlier packaging-only review in which Lean/Lake were unavailable. The Lean source validated here is exactly the `anc/lieb_4433_lean_round8.zip` bundle shipped in this arXiv package.

## Environment

- Lean: 4.19.0 (`6caaee842e94`), arm64-apple-darwin23.6.0
- Lake: 5.0.0-6caaee8
- mathlib revision: `c44e0c8ee63ca166450922a373c7409c5d26b00b`

## Successful checks

- `lake build` — PASS after the pinned dependency cache was supplied locally. The initial attempt failed before compiling project code because GitHub DNS resolution was unavailable.
- `lake build Bridge Bridge.Young` — PASS, final progress 3105/3105.
- `python3 scripts/verify_complete.py` — PASS; 1,489 project theorems audited.
- `python3 scripts/check_generated.py` — PASS; generated certificate sources match exactly.
- `lake env lean validation/round8/FinalAxiomAudit.lean` — PASS.

Across the 83 project Lean files there is no actual use of `sorry`, `admit`, or `sorryAx`, and no hand-written mathematical `axiom`. A dependency traversal over project theorems found no unsafe proof dependency. The transitive mathematical axioms used by the theorems are exactly Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Formalization scope

The final public interface is under `LiebBridge.Young.FinalBridge`. It covers:

- the order-14 integer bridge for `(4,4,3,3)` over all complex Hermitian positive-semidefinite 14-by-14 matrices;
- the exact displayed normalization and positivity/sum of the four rational weights;
- the deduction of `(4,4,3,3)` permanental dominance from four explicitly supplied Pate inequalities.

It does **not** formalize the entire order-14 PDC closure, the order-15 results (including `(3^5)`), the infinite families, or the full theorem through order 15. The four historical Pate inequalities are explicit theorem parameters, not global axioms proved inside this project.

The project proves the literal numerical denominators used in the normalized bridge; it does not separately formalize a general hook-length theorem identifying those numbers with representation dimensions.
