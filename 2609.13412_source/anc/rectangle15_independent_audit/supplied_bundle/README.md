# Order-15 rectangular-immanant proof bundle

Theorem: for every complex Hermitian PSD 15 by 15 matrix A,

    d_(3,3,3,3,3)(A) <= 6006 per(A).

The new branching-refined witness theorem and the complete positivity argument
are in `proof.md`. The integer identity uses 106 central-projector witnesses
and 19 noncentral branching-refined witnesses. It requires no other PDC case.

## Verification

Run:

```sh
python verify.py
```

The verifier uses only the Python standard library. It recomputes every
selected central row from character sums and every branching row from box
contents, then checks all 176 coordinates of the exact integer identity.
It does not read the old cone matrix and does not use an optimization solver,
floating-point arithmetic, or cached binary data.

## Files

`proof.md`: mathematical proof, coefficient definitions, and counting argument.

`certificate.json`: complete positive integer certificate. All coefficient
vectors refer to RAW immanants. The stored scale M and weights z_i satisfy
sum z_i R_i = M (6006 per - d_(3^5)).

`certificate.txt`: full plain-text rendering of every label, coefficient,
and multiplier.

`exact_algebra.py` and `verify.py`: standalone exact coefficient regeneration
and certificate verification.

`verification_log.txt`: output of a successful full verification.

`old_separator.json`: the established separator, retained only for the exact
diagnostic check that a witness used in this proof lies outside the old cone.

`experimental_checks.json`: additional exact small-order tests and numerical
order-15 counterexample-search results; these are not used in the proof.

`selected_central_recheck.json`: record of an additional selected-row
reconstruction using the prior project's coefficient code.

The mathematical positivity proof is not replaced by the arithmetic checker.
This run did not perform an external audit or Lean formalization. The general
branching inequality's historical priority has not been asserted.
