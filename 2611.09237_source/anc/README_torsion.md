# Reconstructing the bounded torsion certificates

This directory contains a complete, deterministic reconstruction of the bounded
integer calculations used in Sections 4 and 5 of the revised manuscript.
Python 3.10 or later is sufficient; only the standard library is used.

## Run

From the source-package root:

```bash
python anc/verify_torsion_certificates.py
```

The program also works when called by its absolute path from any other directory.
By default it writes six certificate files and a summary to the `generated`
subdirectory next to the script. It does not access any unrelated directory.
To perform the complete verification without writing files, run:

```bash
python anc/verify_torsion_certificates.py --verify-only
```

An explicit `--output-dir PATH` selects a different destination. Any failed
verification exits with a nonzero status. Checks remain active with Python's
`-O` option.

Add `--check-stored` to compare all seven supplied JSON files with the complete
deterministic reconstruction. The package-level `verify_all.py` uses both
`--verify-only` and `--check-stored`, so it also validates the distributed data
without rewriting them.

To run every required bounded check, including the independent root-permutation
verification and the type D samples, use:

```bash
python anc/verify_all.py
```

The optional `--extended` argument adds the finite type A diagnostics. Do not
use Python's `-O` option with this entry point: these optional diagnostics use
assertions. The entry point checks `CERTIFICATE_MANIFEST.sha256`, which records
the identities of the six Python programs and eight mathematical-data JSON
files: the seven files under `generated/` and the type A diagnostic record.
All manifest paths are relative to this `anc` directory, so verification also
works when the ancillary directory is downloaded without the manuscript.
The manifest checks file identity separately from the mathematical calculations.

Measured results from a fresh ancillary-file extraction and an isolated virtual
environment are recorded in `verification_results/README.md`, with the complete
program output and machine-readable timing data in the same directory.

## Exact scope

| Root system | Dimensions checked | Nonempty exact-column cases | Result |
| --- | --- | ---: | --- |
| B3 | 3 | 12 | All primitive |
| C3 | 3 | 12 | Eleven primitive; `(121321, 121)` has gcd 2 |
| F4 | 4 | 567 | All primitive |
| C2 | 2 | 3 | Two primitive; `(121, 1)` has gcd 2 |
| G2 | 3 and the complete deletion-gap distribution | 0 in dimension 3 | Every deletion gap is 1 or 2 |
| A3 | 2, 3 | 13, 1 | All primitive |

In B3 and C3 there are 199 distinct single-deletion centre pairs in total:
138 of gap one, 49 of gap two, and 12 of gap three. Thus 61 is the count
of exceptional centres of gap at least two, not the count of all centres.

The F4 dimension-four cases have the exact column-count distribution
497 one-column, 49 two-column, and 21 three-column cases. The new reconstruction
stores 2,594 distinct nonzero raw rows and 660 full-column minors participating
in integral Bezout identities. These numbers describe this reconstruction;
they do not require reproducing an earlier choice of witness minors.

## What is reconstructed and checked

1. Integral simple-root reflection matrices generate each complete Weyl group
   by breadth-first search. Closure under every generator, the group order,
   the maximal reduced length, and generator involutions are checked.
2. The first-arrival word for each element is reduced. Every single deletion is
   evaluated by the Demazure product, retaining every position with a given
   exact centre. The complete centre-gap histogram is checked.
3. For each required pair, all endpoint masks are enumerated. If the length
   difference is `d`, a selected word has length at least `ell(w)-d` with the
   appropriate parity; this permits omission counts of the same parity as
   `d`, at most `d`. The zero-omission mask is excluded because its endpoint
   is `w`, not the strictly smaller `u`.
4. Boundary characters are calculated literally in the simple-root basis:
   at a selected position the character is zero, and at an omitted position it
   is minus the prefix image of the corresponding simple root. Differences
   from one actual reference endpoint mask give the raw integer rows.
   Only zero and duplicate rows are removed; no division or rational
   normalization is performed.
5. Every minor uses every exceptional column and distinct valid row indices.
   Its determinant is computed over the integers. The extended Euclidean
   algorithm records integer coefficients whose combination of the selected
   determinants is the full-column maximal-minor gcd. A gcd of one proves
   primitivity. For the nonprimitive one-column cases, all candidate minors
   are examined and the exact gcd is two.
6. Stored mask endpoints, raw row values, full column sets, minor indices,
   determinants, and Bezout identities are reconstructed and checked again.
   The final expected case counts and gcd histograms must all agree.

The JSON uses one-based word letters, positions, root-coordinate indices, and
minor-row indices. A word digit `1` denotes the first simple reflection.
Each `reference_omitted_positions` or `omitted_positions` list encodes an actual
binary mask by listing precisely its zero positions.

For matrices with more than one column, the maximal-minor gcd is the product
of the nonzero Smith invariants. It need not be the largest invariant.
Here the multicolumn cases are used only when the gcd is one, which makes every
Smith invariant one; the two nonprimitive cases each have one column.

The scripts verify the finite integer calculations. Their interpretation as
degrees of actual curves, the exact exceptional-divisor identification,
field-extension compatibility, and arbitrary-rank induction are proved in
the manuscript; they are not inferred from finite enumeration.
