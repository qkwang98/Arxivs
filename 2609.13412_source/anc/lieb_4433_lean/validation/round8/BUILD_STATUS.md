# Completed order-fourteen bridge: round-eight validation

Date: 2026-09-11. Project: `work/lieb_lean`.

## Mathematical endpoints

All of the following compile in namespace `LiebBridge.Young.FinalBridge`:

- `computed_witness_nonnegative`: exact computed coefficient sum over every partition of fourteen, for each of the twenty witnesses and all complex Hermitian PSD matrices.
- `psd_witness_nonnegative`: the corresponding stored-row certificate form.
- `matrix_bridge` and `bridge_inequality`: unconditional ordinary-immanant bridge.
- `normalized_bridge`: exact displayed convex comparison.
- `pdc4433_of_four_pate`: dominance with precisely the four explicit Pate inputs.

The concrete analytic theorem is `LiebBridge.Young.TensorWitnessPositivity.concrete_witness_nonneg`. The completed actual trace identification remains `LiebBridge.Young.WitnessTrace.trace_witness_eq_computedCoeff`; its established source was unchanged.

No trace, representation, coefficient, positivity, or bridge hypothesis remains in the final matrix bridge. The matrix type is complex and the only matrix premise is `A.PosSemidef`, including singular matrices.

## Build checks

- `lake build Bridge.Young`: **passed**; log `complete_build.log`.
- Independent direct compilation of the frozen `TensorWitnessPositivity.lean` and `FinalBridge.lean`: **passed**; see `INDEPENDENT_AUDIT.md` and `final_bridge_independent_build.log`.
- Isolated `lake build Bridge Bridge.Young`: **passed**, 3105/3105 build jobs; log `clean_build.log`.
- The isolated directory `clean_rebuild/` began with no project build outputs. Its `.lake/packages` is a symlink to the original pinned dependency cache. No original project `.olean` or `.lake/build` was copied.
- All 80 copied Lean/configuration files match `CLEAN_SOURCE_SHA256.json` before and after the build. Existing source and build caches were not cleaned or replaced.
- `python3 scripts/check_generated.py`: **passed**, exact matches for both generated certificate sources; log `generated_sources.log`.
- `python3 scripts/verify_complete.py`: **passed**, all **1,489** imported project theorems, including private/generated declarations. Complete per-theorem output: `../complete/AXIOMS.txt`. The union is exactly `propext`, `Classical.choice`, `Quot.sound`.
- `lake env lean CompleteAudit.lean` in the isolated rebuild: **passed**. `CLEAN_AXIOMS.txt` is byte-for-byte identical to the working inventory: all **1,489** theorems, exactly the same three-axiom union.
- Independent inspection of eight public endpoint types and thirty-two transitive axiom inventories: **passed**; log `final_axiom_audit.log`.

This is a clean rebuild of the complete project source dependency chain, not a rebuild of mathlib from source. A fresh network bootstrap was not performed. It needs access to the pinned toolchain and dependencies; the local build uses their existing cache.

## Preservation

`PRESERVATION.json` confirms:

- All 21 established core/configuration files from round two are byte-for-byte unchanged.
- Among 72 Lean files in the round-eight baseline, only the previously unfinished `Bridge/Young/TensorWitnessPositivity.lean` changed.
- `FinalBridge.lean`, `Bridge/Young.lean`, and the complete inventory tooling are new additions.
- All completed representation theory, trace/coefficient identification, certificate, tensor-permutation, Gram, contraction, normalization, and Pate-interface definitions are preserved.
- The prior README is retained in `README_BEFORE.md`; the current README documents the completed state.

## Interpretation and trust boundary

The actual tensor positivity and trace identities are proved inside Lean. The finite certificate is checked with exact, kernel-checked arithmetic. The final conditional PDC theorem has exactly four theorem parameters: `Pate653`, `Pate644`, `Pate554`, and `Pate5333`, all for the internally defined actual ordinary character family. These interfaces are propositions, not global axioms.

The transitive mathematical axiom union is `propext`, `Classical.choice`, and `Quot.sound`. There is no custom mathematical axiom, `sorryAx`, or native evaluation axiom. The read-only inventory command is not part of proof construction.

The numerical conclusion uses the literal denominators in the requested statement. The certificate's hook-quotient arithmetic does not constitute a separate proof of the general hook-length formula or of numerical actual-tableau dimensions. Actual dimensions cancel in the trace/projector argument; no numerical dimension assumption is required for the explicit displayed inequalities. See the README and independent audit for this precise boundary.

## Reproduction

From the project root:

```sh
lake build Bridge Bridge.Young
python3 scripts/verify_complete.py
python3 scripts/check_generated.py
```

For a new isolated project build using the same pinned package cache:

```sh
python3 scripts/rebuild_isolated.py /tmp/lieb-bridge-clean
```

The destination must not exist. See the README for fresh-environment toolchain and cache commands.
