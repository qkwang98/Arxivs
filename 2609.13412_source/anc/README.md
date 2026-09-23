# Ancillary exact-verification material

This directory accompanies the manuscript.  The large finite certificates are not part of the mathematical exposition in `main.tex`; these files provide the exact data and deterministic verification code.

## Order 14: (4,4,3,3)

Directory: `order14/`

Supports the order-14 bridge and its normalized convex form.  Run:

```sh
cd anc/order14
python verify_all.py
```

The verifier checks all 20 positive weights and all 135 partition coordinates, then runs additional exact character-sum and complex Gram checks.  The universal PSD implication is proved in `complete_proof.md`/`PROOF.md`.

## General partial-swap witnesses and central cones

Directory: `general_witness/`

Supports the Pieri-content formula, the `(m,4,3,3)` family, the seven-witness `(5,4,3,3)` bridge, exact order-14/order-15 central cones, and the order-15 separator.  Run:

```sh
cd anc/general_witness
python verify.py
```

## Order 15 rectangle: (3^5)

Directory: `rectangle15/`

Contains the 125-witness certificate.  Run:

```sh
cd anc/rectangle15
python verify.py
```

The program regenerates all 106 central and 19 branching witnesses and checks all 176 partition coordinates exactly.

## Independent rectangle reconstruction

Directory: `rectangle15_independent_audit/`

Run:

```sh
cd anc/rectangle15_independent_audit
python audit.py
```

The independent audit uses a character-computation route different from the supplied rectangle verifier.  The complete historical audit report is included.  The full central-cone regeneration script is included here as `cone_audit.py`. It requires NumPy and also completed successfully in the current release review. Run `python cone_audit.py` from this directory; `python supplementary_checks.py` runs the independent small-order tests.

## Global structural results

Directory: `global_structure/`

Supports the arbitrary-tail theorem, `(a,b,3,3)` symbolic positivity certificate, node-moving closure enumeration, and structural records.  Run:

```sh
cd anc/global_structure
python verify_symbolic.py
python structural.py
python verify.py
```

`verify.py` is the aggregate verifier.

## Lean order-14 project

`lieb_4433_lean_round8.zip` preserves the pinned Lean project for the order-14 bridge.  Its README describes the exact scope and the pinned Lean/mathlib versions.  The earlier packaging environment did not have Lean installed, but a subsequent final validation rebuilt the full `Bridge.Young` proof chain successfully under Lean 4.19.0 with the pinned mathlib revision.  See `release_verification/lean_final_validation_summary.md` for the checked scope and trust boundary.

## Execution records and historical scope

`release_verification/` contains the current release-review commands, environment, successful logs, and status table. `archived_packaging_logs/` preserves the previous delivery logs, including the earlier full-cone timeout. The latter is superseded by the current successful execution, not edited retroactively.

The README files inside the original certificate directories and the original audit reports describe their own historical sessions. In particular, an old statement that no Lean project or independent audit was then available is not a statement about this combined release. The current Lean archive documents a completed order-14 bridge and a transfer conditional on four historical Pate inequalities; the later final Lean rebuild is summarized in `release_verification/lean_final_validation_summary.md`.

Run Python verifiers without `-O` or `-OO`; assertion checks must remain enabled. The standard verifiers use only Python's standard library. Full cone regeneration additionally uses NumPy, and the general discovery regeneration uses NumPy and SciPy with exact integer arrays, not a numerical optimizer.
