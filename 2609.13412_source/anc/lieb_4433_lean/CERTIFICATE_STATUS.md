# Exact finite certificate: formalization status

The entry point is `Bridge.Certificate`, namespace `LiebBridge.Certificate`.

The following are kernel-checked:

- All twenty rational seminormal path-trace rows agree with the supplied sparse coefficient data on every positive nonincreasing partition of 14.
- The recursive partition enumerator is complete and sound, contains exactly 135 entries, and has no duplicates.
- Every weight is strictly positive. Metadata checks verify contraction count 1 or 2, the correct partition sizes for eta and mu, containment, and sign +1 or -1.
- Every enumerated tableau basis has no duplicates and has exactly 2k boxes. All adjacent axial content differences are nonzero, so no evaluated seminormal reciprocal silently uses division by zero.
- Sparse coefficient lists have distinct keys, nonzero coefficients, and only valid partitions of 14.
- The weighted sparse coefficient cancellation is an equality for **every** `List Nat`, including lists outside the partition domain. The weighted computed coefficient identity follows for every valid partition.
- Hook-formula arithmetic gives the five required numerical values and the sum-of-squares consistency check over all 135 partitions.
- For an arbitrary real-valued function on shapes, the twenty **explicitly assumed** witness inequalities imply the unnormalized five-term bridge.

The rational finite evaluations use `decide +kernel`; none uses `native_decide`. Arithmetic identities use `norm_num` and `ring`. The axiom audit contains only Lean/mathlib's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); there are no new axioms, `sorryAx`, or native-evaluation trust axioms.

## Boundaries

`computedCoeff` is a transparent finite rational tableau calculation. This module does **not** prove that it equals the coefficient obtained from an irreducible symmetric-group character, nor that the twenty real witness forms are nonnegative for actual PSD-matrix immanants. Those links require separate representation-theoretic and positivity arguments.

`hookDegree` is the numerical hook-formula function. Identifying it with irreducible representation dimension requires the hook-length theorem; the finite arithmetic checks do not supply that theorem.

## Reproduction

`python3 scripts/generate_certificate.py` regenerates `Bridge/CertificateData.lean` from the supplied JSON. `python3 scripts/generate_certificate_checks.py` regenerates `Bridge/CertificateChecks.lean`. The algorithm, enumeration proof, and universal linear-identity proof are handwritten.

A clean Lake build is the normal check. For selected modules, `scripts/check_module.py` invokes the pinned project's `lake env lean` in dependency order. `Bridge/CertificateAxiomAudit.lean` prints the finite-certificate axiom dependencies.
