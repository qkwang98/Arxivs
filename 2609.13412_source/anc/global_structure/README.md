# Global structural immanant PDC research bundle

This bundle accompanies `proof.md` (11 September 2026). All PDC statements concern ordinary irreducible immanants of complex Hermitian positive-semidefinite matrices.

## Read first

The results are conditional only on the established mathematical inputs explicitly listed in `proof.md`: the partial-swap/Pieri positivity and balance formulas, the accepted prior finite and infinite PDC results, and Pate's specified classes and node-moving inequality. This is a research proof and exact symbolic certificate, not a Lean formalization or an external audit. Historical priority has not been established against the full Pate literature.

The frontier lists are the complement of the **explicit theorem system S** defined in Section 5 of the proof. They are not lists of all mathematically open cases, not a search of the full arbitrary-filter witness cone, and not a claim that other valid inequalities cannot cover those shapes.

## Reproduce

Use Python 3.10 or newer, without third-party packages:

```sh
python verify.py
```

Do not use Python's `-O` or `-OO` options: this verifier deliberately uses assertions for exact checks.

The successful output is retained in `verification_log.txt`. To regenerate just the symbolic certificate, run:

```sh
python verify_symbolic.py --build
```

To regenerate the frontier count records and residual lists, run:

```sh
python structural.py
```

## Contents

- `proof.md`: complete mathematical proofs, coefficient formulas, scope, and provenance.
- `polynomials.py`: exact sparse polynomial arithmetic over the rationals, and symbolic witness coefficients.
- `verify_symbolic.py`: all-parameter Bernstein/nonnegative-coefficient certificate verification, including the exceptional b=7 slice.
- `symbolic_certificate.json`: the full twenty rational Bernstein polynomials, plus all nineteen exceptional-slice records.
- `core.py`: independent finite-difference witness generation and integer hook-length dimensions, adapted from the supplied earlier bundle. The retained older-family functions are not part of the new symbolic argument.
- `structural.py`: explicit old/new seed systems, node-moving graph closure, and independent analytic membership predicates.
- `frontier_counts.json`: counts for all orders 16 through 30 under the specified systems.
- `residual_shapes.json`: the corresponding residual partition lists.
- `verify.py`: symbolic checks, independent coefficient comparisons, balances, and exhaustive closure/predicate comparisons.
- `verification_log.txt`: output of the full verifier.
- `structural_verification_log.txt`: output of the structural record generation.
- `SHA256SUMS`: file-integrity hashes (not a mathematical validation substitute).

## What is proved and what is only checked in examples

The arbitrary-tail long-first-row theorem is proved in Section 2 by an exact content inequality and induction on tail size. The finite examples in the verifier are supplementary cross-checks.

The two-parameter family `(a,b,3,3)`, `a >= b >= 4`, `5a >= 8b`, has a complete all-parameter symbolic sign certificate. Its two-witness formula is a **uniform recurrence**: subsequent substitution of smaller-b instances proves dominance by a convex combination of Pate-class immanants. It is not a claim that a direct permanent-only certificate always uses just two total witnesses.

The boundary-compression/saturation theorems, node-reachability arguments, and density theorem are mathematical proofs in `proof.md`. The Python program does not formalize their representation-theoretic or asymptotic reasoning.

The displayed failed slope-3/2 example disproves a stronger coefficient-sign ansatz, not PDC itself.
