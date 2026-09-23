# Exact immanant-witness research bundle

The mathematical results, scope qualifications, complete general proofs, and
bibliographic inputs are in `proof.md`. The original order-14 (4,4,3,3) result
is accepted as input and is not reproved. The original twenty witness
definitions were not available; the cone files concern the explicitly defined
central-projector partial-swap construction only.

## Quick exact verification

Use Python 3.10 or later, from this directory:

```sh
python verify.py
```

No third-party package is required. All arithmetic in this verifier is integer
or rational. The run checks:

- The seven-witness order-15 identity, every resulting coefficient, positivity
  of the multipliers, and the four exact normalized weights.
- The degree-bounded polynomial identity for the infinite family; independent
  content-formula checks of its columns; and sample hook-dimension balances.
  Validity for **all** m >= 6 follows from the proof and shifted-polynomial
  sign factorizations, not from the sample checks.
- The additional finite certificates at orders 16 and 17, including all
  witness signs and every coefficient of every retained partition.
- The balance, deduplication, and exact modular-rank certificates of the stored
  order-14 and order-15 generator matrices.
- The exact order-15 separating functional, including all 5398 generators
  and every other order-15 PDC ray.

The general positivity proof is mathematical and is not replaced by these
algebraic checks. `verification_log.txt` records the release verification.
These results have not received an external audit or formal proof-assistant
verification in this run.

## Independent cone regeneration

The quick verifier checks the supplied cone matrices; it does not rebuild
all general-projector character sums. To regenerate those matrices from
Murnaghan–Nakayama characters and marked-cycle enumeration:

```sh
python -m pip install -r discovery/requirements.txt
python discovery/rebuild_and_check.py 14 15
```

This is substantially more expensive than the quick checks. NumPy and SciPy
are required for the original discovery code; all representation-theoretic
arrays use exact Python integers. No floating-point optimization is needed
by the regeneration command. The fresh local `discovery/cache` directory
stores intermediate computations. Delete that directory to force a fresh
regeneration. Do not substitute pickle cache files from an untrusted source.

The regeneration command compares the complete set of primitive rays and
all label/zero counts against the released matrices. It is not limited to
the representative labels stored with the deduplicated rays.

## File formats and normalization

`core.py` implements the content/Newton formula for symmetric-block witnesses.
The coefficient of `d_nu`, not `bar d_nu`, in `witness(p,beta,k)` is the integer
N defined in the proof. `primitive_witness` divides a nonzero vector by the
positive gcd of all its entries. Never mix these two normalizations.

`certificate_order15.json` uses the N normalization. Its integer multipliers
sum to the complete raw-immanant identity recorded in the same file.

`additional_certificates/*.json` uses primitive raw-immanant witnesses.
Each multiplier is an exact rational string; after multiplying the raw
coefficient at nu by f^nu, the total normalized vector is -1 at the target,
the listed nonnegative weights at RHS partitions, and zero elsewhere.
All listed RHS partitions in these additional certificates have three rows.

`cone_14.json.gz` and `cone_15.json.gz` contain ordered partition lists,
primitive raw-immanant rows, one representative parameter label per row,
complete label/zero counts, and a nonsingular-minor certificate modulo the
prime 1000003. A normalized-immanant row is obtained by multiplying each
coordinate by its irreducible dimension. These are generator rays, not a
claimed list of extreme rays.

`dual_15_33333.json` contains 176 integers. They are dual coordinates against
normalized-immanant vectors. Every generator pairs nonnegatively, but the
PDC target per - bar d_(3^5) pairs negatively. This is a cone obstruction,
not a counterexample matrix or a disproof of PDC. The same separator is
nonnegative on all other order-15 PDC rays, so adjoining those bounds does
not remove the obstruction.

`lp_survey_14.json` and `lp_survey_15.json` are floating-point discovery logs.
Their success/infeasibility statuses are **not** exact certificates. In
particular, numerical difficulties are not mathematical exclusions.

## Scope of novelty

Tensor-contraction and central-witness approaches have substantial precedents
in Pate and in the operator/entanglement literature. The explicit theorems
and certificates here are derived and checked in this run. Their historical
priority has not been established by an exhaustive review of older papers.
The new PDC corollaries use the known classes and node-moving theorem cited
in `proof.md`.
