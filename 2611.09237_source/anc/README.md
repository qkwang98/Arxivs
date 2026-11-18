# Ancillary material

**The Woo–Yong conjecture**  
Minghua Dou, 6 November 2026

This directory accompanies the same arXiv version of the manuscript. Download
and unpack the complete article source to preserve the directory structure.
The programs use only Python 3.10 or later and its standard library; no package
installation or network access is required to run them.

## Run the verification

From the root of the unpacked source archive:

```bash
python anc/verify_all.py
```

The default run checks the program/data manifest, reconstructs the bounded
integer certificates, compares all seven supplied certificate JSON files with
that reconstruction, checks the witnesses using independent Euclidean-root
permutations, and checks the finite type D identities.

To include the optional finite type A diagnostics:

```bash
python anc/verify_all.py --extended
```

The scripts also work when invoked by absolute path from a different working
directory. Do not use Python's `-O` option: the optional type A diagnostics use
assertions, and the entry point explicitly rejects optimized mode. A failed
check gives a nonzero exit status. A successful run ends with:

```text
ALL REQUESTED CHECKS PASSED.
```

For an isolated invocation, the corresponding commands are:

```bash
python -I -B anc/verify_all.py
python -I -B anc/verify_all.py --extended
```

The `-I` option excludes user site packages and ignores Python environment
settings; `-B` prevents bytecode-cache files. The entry point uses these options
for its verification subprocesses as well.

## Files

| File or directory | Role |
| --- | --- |
| `verify_all.py` | Unified entry point, file-identity checks, and elapsed times |
| `verify_torsion_certificates.py` | Exact reconstruction of the A3/B3/C3/C2/F4/G2 inputs |
| `verify_root_permutations.py` | Independent implementation with explicit Euclidean roots |
| `verify_type_d.py` | Finite samples of the type D identities |
| `check_type_a.py` | Filtered-maximum diagnostics in S6 and S7 |
| `check_type_a_auxiliary.py` | Horizontal incidence, greedy lifts, and complete prefixes in S6 |
| `generated/` | Six root-system certificates and their summary, all in JSON |
| `type_a_independent_diagnostics.json` | Recorded finite type A diagnostic counts |
| `README_torsion.md` | Certificate conventions and exact mathematical scope |
| `CERTIFICATE_MANIFEST.sha256` | SHA-256 identities of the six programs and eight supplied JSON files |
| `SOURCE_MANIFEST.sha256` | Identities of this complete manuscript/source distribution |
| `verification_results/` | Actual execution output, environment, timings, and measurement method |

`CERTIFICATE_MANIFEST.sha256` uses paths relative to `anc/`; `verify_all.py`
checks it automatically. `SOURCE_MANIFEST.sha256` uses paths relative to the
source-package root and covers the manuscript and ancillary files, excluding
only itself. On a system with `sha256sum`, it can be checked from that root with:

```bash
sha256sum -c anc/SOURCE_MANIFEST.sha256
```

The manifests identify the supplied bytes. The verification programs carry out
the mathematical calculations separately. If the source is deliberately
edited, the corresponding manifest must be regenerated before identity checks
can pass.

## Reconstruct the certificates separately

The following command checks the stored data without overwriting it:

```bash
python anc/verify_torsion_certificates.py --verify-only --check-stored
```

To produce a new reconstruction in a separate directory:

```bash
python anc/verify_torsion_certificates.py --output-dir reconstructed_certificates
```

Without `--verify-only` or an explicit output directory, this program writes
to its adjacent `generated/` directory. The unified entry point never rewrites
the supplied certificates.

## Actual execution record

The archived default and extended runs were performed on 6 November 2026 using
CPython 3.12.14 on Ubuntu 24.04.3 LTS (x86_64), on a host reporting an AMD EPYC
9V74 processor. A new archive extraction and a fresh virtual environment
without pip or third-party distributions were used. Both invocations ran from
working directories separate from the extracted package and exited with status
zero.

The measured whole-command wall times were **2.322623 seconds** for the default
run and **33.255628 seconds** for the extended run. Each is a single observed
serial run; these times will vary with the machine and its load. Complete
outputs are in `verification_results/default_stdout.txt` and
`verification_results/extended_stdout.txt`. The JSON records retain the
environment, timing scope, per-task times, exit status, and hashes of the
program/data manifest and output.

## Scope of the computations

The finite inputs required for Proposition 5.1 are reconstructed, including all
567 F4 gap-four centre pairs. The certificate documentation states the root and
index conventions and explains the exact columns, integer rows, maximal minors,
and integral Bezout identities. The independent root-permutation implementation
does not import the Cartan-matrix implementation.

The optional type A diagnostics cover 417 filtered-maximum cases in S6 and
4,998 in S7; the S6 auxiliary checks cover 347,542 horizontal-incidence
comparisons, 29,968 greedy lifts, and 4,096 complete prefix witnesses. These
are finite checks of the manuscript's geometric argument. The arbitrary-rank
claims, field-extension statements, and interpretation of the integer matrices
as geometric degrees remain the proofs given in the manuscript.

## Compile the manuscript

From the source-package root, run:

```bash
latexmk -pdf main.tex
```

The document uses `amsart`, standard TeX Live packages, and BibTeX's `alpha`
style. Both `references.bib` and the matching `main.bbl` are supplied. No
shell-escape operation or execution of the Python programs is needed to compile
the paper. The corresponding arXiv processor is `pdflatex`, with `main.tex` as
the top-level document.
