# Independent audit of the order-15 rectangular immanant certificate

Audit date: 11 September 2026.

## Verdict and scope

The supplied branching-refined positivity proof and its trace/content formula are mathematically valid. Both the supplied verifier and a separately written verifier passed. All 106 central and 19 branching primitive vectors were regenerated, all positive integer multipliers were checked, and the identity was verified on all 176 partition coordinates. The result proves

    d_(3,3,3,3,3)(A) <= 6006 per(A)

for arbitrary complex Hermitian positive-semidefinite matrices, including singular matrices. No other PDC case is used in this certificate.

The full central cone was also reconstructed independently: 8112 parameter labels, 1310 zero labels, and 5398 distinct nonzero primitive rays. The minimum separator pairing was 98. Used term 120 has raw dimension-weighted pairing -116616500, or -2330 after division by 50050. Its escape from the central cone, including the stated enlargement, is certified.

The seven-witness bridge for (5,4,3,3) was checked both from the content formula and the defining character sums on every coordinate. Its normalized weights are 630,791,54,10 divided by 1485. Together with Pate's stated partition class and node-moving theorem, this closes order 15. The broader statement “through order 15” also uses the preceding note's explicitly accepted order-14 (4,4,3,3) input. Its proof was not among the uploaded materials and is not independently audited here.

Historical priority is NOT fully settled by this audit. The reciprocal-content diagonal coefficient is classical Young representation theory. Tensor contraction and operator formulations have established antecedents. No earlier explicit (3^5) proof was located, but the older Pate full texts were not all accessible. In particular, the quantitative condition in Pate 1999's separate (n+p,n^k) family still needs inspection before excluding that theorem as an earlier source.

## Run the checks

Use an ordinary Python invocation, not Python -O or -OO. The independent scripts refuse optimized execution, because exact assertions are part of the checks.

From this directory:

```sh
python supplied_bundle/verify.py
python audit.py
python supplementary_checks.py
python cone_audit.py
```

The first three commands require only the Python standard library. The last command additionally requires NumPy. NumPy is used with `dtype=object` exclusively for arbitrary-precision Python-integer matrix arithmetic; it does not perform floating-point certificate verification.

`audit.py` and `cone_audit.py` optionally accept a different proof-bundle directory as their first argument. By default they read `supplied_bundle` next to the scripts. No network access or optimization solver is required.

## Independence of the reconstruction

None of the independent scripts imports the supplied `exact_algebra.py` or `verify.py`.

* Characters are reconstructed through Jacobi-Trudi expansions and induced trivial characters computed by assigning distinguishable permutation cycles to labelled row capacities. This is a different character algorithm from the supplied Murnaghan-Nakayama implementation.
* Dimensions are computed by recursively removing Young-diagram corners, separately from the supplied hook-length routine.
* Central character sums are regenerated with concrete permutation representatives: block permutations and swaps are composed on all 15 actual labels, and their cycles are traversed directly. The supplied composed-marked-cycle length formula is not used. Both implementations do use the same mathematically justified orbit compression principle.
* The orbit enumerator is independently compared with exhaustive permutation enumeration in 12 small block configurations: every allowed swap number for (2,3), (3,3), (3,4), and (4,4).
* All selected k=1 sums are also compared with the Littlewood-Richardson/content-difference expression. Forty-three selected symmetric-block rows are additionally compared with the content polynomial formula.
* Every branching vector is independently regenerated. There are also 209 direct group-algebra trace comparisons at orders 2 through 6, not using the content formula to compute the direct trace.
* The full-cone script generates its counts afresh and never reads a supplied cone matrix or a stored generator cache.

## Files

`audit.py`: independent 125-witness verification.

`cone_audit.py`: independent enumeration and separation check for the full central cone.

`supplementary_checks.py`: seven-witness bridge, all small-order direct branching traces, and partition-class enumeration through order 15.

`*_results.json`: machine-readable outputs.

`*_verification.log`: actual independent run logs.

`supplied_verifier_rerun.log`: actual rerun of the original verifier.

`supplied_bundle/`: unmodified copies of the uploaded proof bundle. These are input data and supplied code, not independently authored code.

`preceding_theory_note.md`: the other uploaded note, preserved to document the bridge and the accepted order-14 dependency.

`source_integrity.json`: input checksum results.

`environment.json`: the runtime used in this audit.

`literature_priority.md`: what the literature check did and did not establish.

`SHA256SUMS.txt`: checksums of this audit package's files, excluding the manifest itself.

The arithmetic logs certify finite identities. Universal positivity is supplied by the separately audited tensor argument; neither random PSD tests nor floating-point feasibility is a proof dependency. This is not a Lean formalization or an external human-referee endorsement.
