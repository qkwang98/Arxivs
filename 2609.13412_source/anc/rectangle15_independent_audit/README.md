# Rectangle-15 independent audit reproducibility archive

Audit date: 11 September 2026.

## Purpose

This archive preserves the independent audit of the proposed final ordinary-immanant permanental-dominance case at order 15,

```text
d_(3,3,3,3,3)(A) <= 6006 per(A),
```

for every complex Hermitian positive-semidefinite `15 x 15` matrix `A`, including singular matrices.

The audit concluded that the theorem is mathematically proved by the supplied positivity argument and exact 125-witness certificate. Historical novelty is a separate question: the reciprocal-content representation-theoretic mechanism has classical antecedents, and the audit did **not** fully establish whether every form of the branching-refined mechanism or the explicit `(3^5)` consequence is absent from all older Pate literature.

For the full mathematical verdict, read `independent_audit_report.md`.

## What was independently checked

The audit independently checked, rather than merely accepting stored witness rows:

- the branching-refined projection `b = e_beta^(n-1) e_gamma^(n-2)` and its orthogonal-projection property;
- the complex squared-norm positivity of `W = b s b`, `s=(n-1,n)`;
- the identity `s J_n - J_(n-1) s = 1`;
- Young branching and Jucys–Murphy content eigenvalues;
- the trace formula `f^gamma / (content difference)` and the nonzero-denominator claim;
- normalization from irreducible traces to raw immanants;
- coverage of all complex Hermitian PSD matrices, including singular ones;
- all 106 selected central witnesses and all 19 branching-refined witnesses;
- positivity of all 125 integer multipliers;
- primitive normalization and exact dimension balance;
- all 176 partition coordinates of the final certificate;
- the exact target coefficients `6006 M` at `(15)` and `-M` at `(3,3,3,3,3)`;
- `f^(3,3,3,3,3) = 6006`;
- the full order-15 central cone: 8112 parameter labels, 1310 zero labels, 5398 distinct nonzero primitive rays;
- nonnegative separator pairing on every regenerated central ray, with minimum 98;
- negative separator pairing for the selected branching term 120, proving that it genuinely lies outside the old central cone;
- the seven-witness bridge for `(5,4,3,3)` and the order-15 closure logic;
- 209 small-order direct trace comparisons for the branching/content formula.

## Independence of the main verifier

`audit.py` is the actual independent verifier used in the audit. It deliberately does not use the supplied character implementation.

Its key independent choices are:

- characters via Jacobi–Trudi expansion plus induced trivial characters computed by assigning permutation cycles to labelled row capacities, rather than the supplied Murnaghan–Nakayama implementation;
- dimensions via recursive Young branching rather than the supplied hook-length routine;
- central swap sums via concrete permutations on all 15 labels and direct cycle traversal, rather than the supplied composite marked-cycle-length formula.

Both implementations share the mathematically justified orbit-compression principle. The independent audit separately checked that compression against exhaustive permutation enumeration in 12 small block configurations.

## Original inputs versus audit outputs

Original proof inputs are preserved under `supplied_bundle/` and as `preceding_theory_note.md`. They are **inputs**, not independently authored audit code. See `SOURCE_MANIFEST.md` for the exact mapping to the externally uploaded filenames:

- `rectangle15_exact_proof_bundle.zip`
- `rectangle15_complete_proof.md`
- `immanant_witness_theory_and_new_family.md`

The outer original proof ZIP is not nested inside this archive; its full audited contents are preserved unmodified under `supplied_bundle/`.

Independent audit outputs include the independent scripts, result JSON files, run logs, cone regeneration data, literature-priority notes, and the consolidated audit report.

## Requirements

The audit was originally run under:

- Python 3.13.5
- Linux x86_64
- NumPy 2.3.5

`audit.py` and `supplementary_checks.py` require only the Python standard library.

`cone_audit.py` additionally requires NumPy. NumPy is used with `dtype=object` for arbitrary-precision Python-integer matrix arithmetic; no floating-point certificate decision is made by the cone verifier.

Do **not** run the independent scripts with `python -O` or `python -OO`; they intentionally use exact assertions as verification checks.

## How to run

From the `rectangle15_independent_audit/` directory:

```sh
python supplied_bundle/verify.py
python audit.py
python supplementary_checks.py
python cone_audit.py
```

The first command is the original supplied verifier. The next three are the independent audit scripts.

Expected successful independent output includes lines such as:

```text
PASS: independent Jacobi--Trudi character tables and branching dimensions, n=0..15
PASS: 19 branching witnesses regenerated independently
PASS: all 125 stored rows agree, primitive signs preserved, all weights positive, all 176 final coordinates exact
PASS: term 120 separator pairing -116616500, normalized -2330
```

The cone verifier should end with JSON containing:

```json
{
  "status": "PASS",
  "labels": 8112,
  "zero_labels": 1310,
  "distinct_nonzero_rays": 5398,
  "minimum_primitive_raw_separator_pairing": 98,
  "target_normalized_pairing": -300
}
```

## Historical and packaging-time logs

Files named `independent_verification.log`, `cone_verification.log`, and `supplementary_verification.log` are the logs preserved from the original audit session.

The independent source filenames are the original audit-session names: `audit.py` is the main independent verifier and `cone_audit.py` is the full central-cone verifier. They were not renamed so that the package preserves the exact code used.

During final packaging, the supplied verifier was also rerun from `supplied_bundle/verify.py`; its fresh output is `supplied_verifier_packaging_rerun.log` and ends with `ALL EXACT CHECKS PASSED.`

Files named `independent_verification_log.txt`, `cone_verification_log.txt`, and `supplementary_verification_log.txt` are fresh reruns performed from the packaged copy during creation of this archive.

The original result files `independent_results.json`, `cone_results.json`, and `supplementary_results.json` are preserved byte-for-byte. Freshly generated JSON from the packaging-time rerun is stored separately as `*_rerun.json`.

## Scope and caveats

The audit establishes mathematical correctness of the `(3^5)` theorem and its exact certificate, subject only to the mathematical proof and certificate actually audited.

The statement that ordinary-immanant PDC is complete **through order 15** also relies on the project's previously accepted order-14 `(4,4,3,3)` result. Its proof was not in the supplied files and is not independently audited in this archive.

Historical priority is not fully settled. In particular:

- the reciprocal adjacent-content coefficient is classical Young/seminormal representation theory;
- tensor-contraction and operator formulations have substantial antecedents;
- not all four requested older Pate papers were available in full text;
- the quantitative hypotheses of Pate 1999's separate `(n+p,n^k)` family should be checked before making an unconditional novelty claim for `(3^5)`.

These historical questions do not affect the mathematical validity of the exact proof audited here.

## Integrity

`SHA256SUMS` contains SHA-256 hashes for every packaged file except `SHA256SUMS` itself. `SHA256SUMS_original_audit.txt` preserves the checksum manifest from the previous audit package.
