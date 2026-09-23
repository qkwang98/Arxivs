# Source manifest

This archive packages the independent audit performed on 11 September 2026. It distinguishes original proof inputs from independently generated audit outputs.

## Original proof/certificate inputs audited

### External upload: `rectangle15_exact_proof_bundle.zip`

This was the primary exact proof/certificate bundle. The outer ZIP is **not duplicated as a ZIP file inside this reproducibility archive**. Its contents were copied without modification into:

`supplied_bundle/`

Those preserved files are:

- `supplied_bundle/README.md`
- `supplied_bundle/certificate.json`
- `supplied_bundle/certificate.txt`
- `supplied_bundle/exact_algebra.py`
- `supplied_bundle/experimental_checks.json`
- `supplied_bundle/old_separator.json`
- `supplied_bundle/proof.md`
- `supplied_bundle/selected_central_recheck.json`
- `supplied_bundle/verification_log.txt`
- `supplied_bundle/verify.py`
- `supplied_bundle/SHA256SUMS.txt`

`source_integrity.json` records the checksum comparison performed during the audit. Every checked bundled file matched the supplied bundle's own checksum manifest.

### External upload: `rectangle15_complete_proof.md`

This standalone Markdown proof was audited as a source input. During the audit it was byte-compared with `supplied_bundle/proof.md`; `source_integrity.json` records:

`"uploaded_markdown_equals_bundled_proof": true`

The standalone external filename is not separately duplicated because its exact contents are already preserved as `supplied_bundle/proof.md`.

### External upload: `immanant_witness_theory_and_new_family.md`

This preceding theory note was used for the seven-witness bridge, the partition-class enumeration, and the explicitly accepted order-14 dependency. Its contents are preserved as:

`preceding_theory_note.md`

The note itself states that the order-14 result for `(4,4,3,3)` is accepted input rather than reproved there.

## Independently generated audit code

The following scripts were actually used in the independent audit and are preserved verbatim from the prior audit archive:

- `audit.py` — independent 125-witness verification, using Jacobi–Trudi/induced-character reconstruction rather than the supplied Murnaghan–Nakayama implementation.
- `cone_audit.py` — independent regeneration of the complete order-15 central-projector cone and separator check.
- `supplementary_checks.py` — independent seven-witness bridge checks, direct small-order branching trace comparisons, and partition-class enumeration.

These scripts do not import `supplied_bundle/exact_algebra.py` or `supplied_bundle/verify.py` for their independent algebra.

## Independently generated audit outputs

Historical outputs from the original audit session, preserved exactly:

- `independent_results.json`
- `cone_results.json`
- `supplementary_results.json`
- `independent_verification.log`
- `cone_verification.log`
- `supplementary_verification.log`
- `supplied_verifier_rerun.log`
- `environment.json`
- `source_integrity.json`
- `literature_priority.md`

Fresh packaging-time rerun outputs are separately named with `_rerun` and `_log.txt` suffixes so that the original result JSON files remain byte-for-byte unchanged.

## Audit report versus source inputs

`independent_audit_report.md` is the consolidated mathematical verdict from the conversation. It is an audit output, not an original proof input.

The archive does not claim that any unavailable paper or proof was present. In particular, the original proof of the accepted order-14 `(4,4,3,3)` case was not supplied and is not silently reconstructed here.

## External input SHA-256 identifiers

The externally uploaded source files used for this audit had these SHA-256 hashes:

```text
764a901f4da5609068bcd2126b8b6a9993cc910d4afd207c2fc6e26cd5b57d29  rectangle15_exact_proof_bundle.zip
501f9a722f803a4764eefa2f1bf71278a0f30e15ba49442173ae507f3e7fd8f8  rectangle15_complete_proof.md
3fa8570357e1996c7a86d6da67fcc4babcce654a8e0baffb93b3177a42f366f1  immanant_witness_theory_and_new_family.md
```

The outer ZIP is identified here by hash rather than nested as a second ZIP; its audited contents are present under `supplied_bundle/`.
