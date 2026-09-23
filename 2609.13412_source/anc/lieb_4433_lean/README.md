# Order-fourteen ordinary-immanant bridge in Lean

The bridge is proved for every complex Hermitian positive-semidefinite
14 × 14 matrix, including singular matrices. The completed entry point is
`Bridge.Young`; the public results are in `Bridge/Young/FinalBridge.lean`.
The final permanental-dominance conclusion assumes only the four explicitly
named Pate interfaces. Neither the bridge nor witness positivity is an
external assumption.

For the internally constructed ordinary Young characters, Lean proves

\[
59512d_{4433}(A)\le
4035d_{653}(A)+6725d_{644}(A)+39759d_{554}(A)+23636d_{5333}(A).
\]

It also proves the exact comparison

\[
\frac{d_{4433}(A)}{12012}\le
\frac{20175}{238048}\frac{d_{653}(A)}{15015}+
\frac{20175}{238048}\frac{d_{644}(A)}{9009}+
\frac{79518}{238048}\frac{d_{554}(A)}{6006}+
\frac{118180}{238048}\frac{d_{5333}(A)}{15015}.
\]

All four weights are positive and their sum is exactly one.

## Public theorems

All names below have prefix `LiebBridge.Young.FinalBridge.`:

- `computed_witness_nonnegative`: for every `w ∈ Certificate.rows` and every
  `A : Matrix14` with `A.PosSemidef`, the sum over **all partitions of 14** of
  `(computedCoeff w p : ℝ) * OrdinaryImmanants.immanant p A` is nonnegative.
- `psd_witness_nonnegative`: the same positivity in the stored certificate-row
  form used by the weighted cancellation theorem.
- `matrix_bridge`: a proof of `Bridge4433 OrdinaryImmanants.character`.
- `bridge_inequality`: the displayed integer-coefficient bridge.
- `normalized_bridge`: the displayed exact rational comparison.
- `pdc4433_of_four_pate`: under the four Pate arguments below,
  `OrdinaryImmanants.immanant [4,4,3,3] A / 12012 ≤ permanent A`.

`OrdinaryImmanants.character` is fixed internally from the verified Young
representations. It is not supplied by the caller. `Matrix14` is a complex
matrix type; `A.PosSemidef` includes Hermitianity. There is no real-entry,
positive-definiteness, rank, nonzero-vector, or genericity hypothesis.
The immanant's real-valued interface agrees with its complex expression on
Hermitian matrices by the established reality theorem.

## Formal proof and module boundaries

1. `Bridge/Young/` constructs standard tableaux, adjacent-transposition
   matrices, the symmetric-group representations, irreducibility, characters,
   prefix projectors, branching, and the finite tableau trace formula.
   `WitnessTrace.trace_witness_eq_computedCoeff` identifies the **actual**
   operator trace with the actual eta-module dimension times `computedCoeff`.
   This identification is proved, not assumed or replaced by a Boolean table.
2. `Bridge/Young/TensorWitnessPositivity.lean` connects the concrete
   coefficient-defined tensor operator to the localized projectors and swaps.
   `TensorWitnessPositivity.concrete_witness_nonneg` proves its expectation
   nonnegative on arbitrary complex pure tensors in arbitrary finite dimension.
   Its proof invokes the explicit contraction/squared-norm identities in
   `Bridge/Contraction.lean`, after proving the required concrete projector
   properties. No positivity premise is passed into this public theorem.
3. `TensorPairing.lean`, `WitnessCoefficientPositivity.lean`, and
   `FinalBridge.lean` connect tensor expectations, actual character traces,
   central averaging, and immanants. `TensorGram.lean` supplies Gram
   factorization on the entire complex PSD cone, including singular matrices.
4. The preserved `Certificate*.lean` modules check all twenty rational rows,
   their positive weights, and exact cancellation on every partition of 14.
   Their finite computations use exact arithmetic and kernel-checked proofs.
5. `Normalization.lean` proves the exact arithmetic conversion and convex
   weight facts. `PateInterfaces.lean` supplies the four proposition interfaces;
   `FinalBridge.lean` instantiates its generic transfer with the proved bridge.

### Numerical degree boundary

The certificate checks the hook-quotient arithmetic yielding
`12012, 15015, 9009, 6006, 15015` for the five specified shapes. This project
**does not separately prove a general hook-length formula or the numerical
identification of these five values with the cardinalities of the actual
standard-tableau bases**. Actual dimensions in the representation/projector/
trace chain are tableau cardinalities; those dimensions cancel in the proof.
The normalization and four Pate interfaces use the literal denominators shown
above, so every displayed inequality is proved exactly as stated without an
additional dimension assumption. Do not interpret the numerical hook checks
as a separately formalized dimension theorem.

## Exact trust boundary

The bridge, the twenty witness inequalities, and the normalized comparison
have no external mathematical hypotheses beyond their displayed matrix and
row-membership premises. Their transitive Lean axiom dependencies are exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

These are standard Lean foundations. There is no `sorryAx`, custom
mathematical axiom, unsafe cast, or native-evaluation axiom in the proof chain.
The full inventory of **1,489** project theorems is produced by `CompleteAudit.lean` and saved
as `validation/complete/AXIOMS.txt`. The inventory covers every theorem owned
by a project module imported through `Bridge.Young`, including private and
generated declarations, and rejects any other axiom. The audit command is
read-only metaprogramming; it is not a proof-producing evaluation mechanism.

The final PDC theorem takes precisely these four additional mathematical
arguments, all for `OrdinaryImmanants.character`:

- `LiebBridge.Pate653`: for every complex PSD `A`, `d653(A) / 15015 ≤ per(A)`.
- `LiebBridge.Pate644`: for every complex PSD `A`, `d644(A) / 9009 ≤ per(A)`.
- `LiebBridge.Pate554`: for every complex PSD `A`, `d554(A) / 6006 ≤ per(A)`.
- `LiebBridge.Pate5333`: for every complex PSD `A`, `d5333(A) / 15015 ≤ per(A)`.

These are explicit theorem parameters, not global Lean axioms. Historical
proofs of these four propositions are outside this project. No bridge, trace,
character-identification, or witness-positivity assumption remains.

## Reproducible build

Pinned versions:

- Lean: `leanprover/lean4:v4.19.0` (`lean-toolchain`).
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All transitive package revisions: the preserved `lake-manifest.json`.

From the project root with `elan` installed:

```sh
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
lake build Bridge Bridge.Young
python3 scripts/verify_complete.py
python3 scripts/check_generated.py
```

Keep `lake-manifest.json`; do not update dependency revisions. A fresh machine
needs network access to obtain the pinned toolchain, packages, and mathlib
cache. The Python commands require only Python 3's standard library. Python
is used for reporting and generated-source comparison, not mathematical proof.

For the completed results in another Lean file:

```lean
import Bridge.Young

#check LiebBridge.Young.FinalBridge.computed_witness_nonnegative
#check LiebBridge.Young.FinalBridge.bridge_inequality
#check LiebBridge.Young.FinalBridge.normalized_bridge
#check LiebBridge.Young.FinalBridge.pdc4433_of_four_pate
```

A plain `lake build` retains the established historical default target
`Bridge`; use the explicit `Bridge.Young` target to build the completed chain.
The original `Bridge.lean`, `Audit.lean`, and earlier checkpoint reports are
preserved and may describe the formerly incomplete state. They are superseded
by this README and the round-eight validation record, not edited retroactively.

## Validation and preservation

See `validation/round8/BUILD_STATUS.md` for the final build, isolated clean
project rebuild, axiom inventory, and preservation results. The independent
review is in `validation/round8/INDEPENDENT_AUDIT.md`.

To repeat the isolated rebuild without changing the working cache, choose a
new destination that does not exist:

```sh
python3 scripts/rebuild_isolated.py /tmp/lieb-bridge-clean
```

The isolated rebuild starts without any project build outputs and reuses the
pinned dependency cache. It is a clean rebuild of this project's Lean sources,
not a fresh network bootstrap or a rebuild of mathlib from source.

All 21 files in `validation/round2/ESTABLISHED_SHA256.json` remain byte-for-byte
unchanged. Among the 72 Lean sources recorded at the start of round eight,
only the previously unfinished `TensorWitnessPositivity.lean` was changed.
The completed representation theory, trace/coefficient identification,
certificate, Gram, contraction, normalization, and Pate-interface files were
preserved. New assembly and audit files are separate additions. The previous
README is retained as `validation/round8/README_BEFORE.md`.
