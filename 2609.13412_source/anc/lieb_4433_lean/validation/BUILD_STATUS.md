# Validation record

Date: 2026-09-11.

The delivered artifact is a **partial formalization**. Successful compilation
does not change the unproved ordinary-character/branching boundary described
in the README and independent audit.

| Check | Observed result |
| --- | --- |
| Normal `lake build` | Passed; root `Bridge` and all imported modules built |
| Isolated source rebuild | Passed with no pre-existing project build outputs |
| Identity of Lean sources with isolated rebuild | Every delivered Lean module and `Audit.lean` matched byte-for-byte |
| `python3 scripts/check_generated.py` | Both generated Lean files matched exactly |
| `python3 scripts/check_axioms.py` | Passed for all 115 public theorem entries in `Audit.lean` |
| Axiom dependencies | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Native-evaluation/custom proof axioms | None in the audited theorem dependencies |
| Supplied archive comparison | `FINAL_PROOF.md`, `FILES.md`, `REVIEW_SCOPE.md`, and `certificate.json` matched the archive byte-for-byte |
| Cached mathlib source | Clean Git worktree at the pinned revision |

Environment observed:

```text
Lean 4.19.0
Lean commit 6caaee842e94
arm64-apple-darwin23.6.0
mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b
```

The isolated build copied the project's sources into a separate directory and
reused a copy of the existing, pinned mathlib/dependency cache. It started
without this project's `.lake/build` directory and rebuilt the project from
source. Its full output is `CLEAN_BUILD.log`.

A fresh internet download of elan, mathlib, and all dependencies was **not**
performed. The README provides the pinned clean-install commands; the tested
reproducibility claim here is the isolated source rebuild with the pinned
dependency cache. The source archive does not include that multi-gigabyte
cache.

The compiler emitted harmless unused-section-variable linter warnings in
some generic lemmas; there were no build errors or admitted-proof warnings.

`AXIOMS.txt` contains the complete theorem dependency report.
`SPECIFICATION_PROVENANCE.json` records the supplied archive hash, preserved
source hashes, and independent-audit source task identifier. The two Python
verification helpers are provenance/trust checks, not substitutes for Lean
proofs.
