# 4433 Lean project — completed round-eight source bundle

This archive contains the validated Lean project, exact certificate and proof
specification, build scripts, complete axiom inventory, independent audit,
and historical checkpoint records. Read `README.md` for the current status.

Completed entry point: `Bridge.Young`.

```sh
lake exe cache get
lake build Bridge Bridge.Young
python3 scripts/verify_complete.py
python3 scripts/check_generated.py
```

Lean is pinned to `leanprover/lean4:v4.19.0`. Install elan and the pinned
toolchain first if needed. Keep `lake-manifest.json` unchanged.

The bridge is unconditional for all complex Hermitian PSD 14 × 14 matrices.
The final PDC theorem has only four explicit Pate theorem parameters.
The complete inventory covers 1,489 project theorems and contains exactly
propext, Classical.choice, and Quot.sound.

This is a portable SOURCE bundle. It excludes `.lake` dependencies/build
outputs, Python caches, and the duplicate isolated `clean_rebuild` directory.
Clean-build logs, the clean source manifest, and both complete axiom inventories
are included. A fresh machine needs network access for pinned dependencies.
The original project and caches were not modified when packaging.

`BUNDLE_SHA256SUMS.txt` checks every payload file except itself. Earlier source
manifests are preserved historical records, not manifests of this whole bundle.
All 80 source/configuration files in the round-eight clean-build manifest were
checked against their validated hashes before packaging.

Read the numerical-degree qualification in README.md: literal requested
normalization is proved; a separate general hook-length/dimension theorem is
not claimed.
