# Exact certificate for permanental dominance of (4,4,3,3)

## Claimed theorem

For every complex Hermitian PSD matrix A of order 14,

    d_(4,4,3,3)(A) / 12012 <= per(A).

The argument proves the exact intermediate inequality

    59512 d_(4,4,3,3)
      <= 4035 d_(6,5,3) + 6725 d_(6,4,4)
         + 39759 d_(5,5,4) + 23636 d_(5,3,3,3).

After character-degree normalization its four right-hand coefficients form
positive weights summing to one. Pate's previously established theorem covers
the four right-hand partitions and therefore finishes the proof.

This is the complete ordinary-immanant case (4,4,3,3), not the full
all-orders/all-subgroups Lieb conjecture.

## Read first

`PROOF.md` gives the arbitrary-PSD partial-transpose positivity lemma, the
finite trace formula, all 20 positive weights, every expanded witness,
the final cancellation identity, the known-theorem dependency, and audit scope.

## Run verification

Requires Python 3 and only its standard library. From this directory:

    python verify_all.py

The verifier exits with an error if any exact assertion fails. It does not
invoke or trust a linear programming solver. It performs no network requests.

## Contents

- `certificate.json`: all 20 parameter tuples, positive rational weights,
  exact coefficient rows and the final five-term coefficient identity.
- `verify_certificate.py`: regenerates all rows in both rational seminormal
  and orthogonal Young forms; checks all 135 partitions, hook degrees,
  normalized convex weights and known-case coverage.
- `operator_identity_checks.py`: exact Gaussian-rational test of the partial
  transpose sandwich and complex-product expectation identities.
- `adversarial_exact_checks.py`: literal symmetric-group character sums at
  small orders, plus an exact complex rank-13 Gram stress test. The character
  calculations use Murnaghan--Nakayama rather than Young representation traces.
- `adversarial_fan_output.json`: exact output for the rank-13 example.
- `verify_all.py`: one-command entry point.
- `verification_output.txt`: the successful local verification transcript.
- `SHA256SUMS.txt`: hashes of these files, excluding the manifest itself.

## What verification means here

The exact finite identities have passed all bundled checks. The universal
positivity statement is an analytic proof in `PROOF.md`, not a finite random
search. Conversely, the arithmetic verifiers are not a formalization of all
that analytic proof in a trusted proof-assistant kernel.

All proof construction and checks were local. No external peer review,
parallel independent-agent audit, or Lean/Isabelle verification is claimed.
The theorem and certificate should be scrutinized as a newly derived proof.
