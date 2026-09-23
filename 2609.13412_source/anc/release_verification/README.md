# Current release verification

All statuses in `verification_results_final.json` are fresh executions against isolated clean copies of the supplied source directories. Assertions were enabled. Original mathematical scripts and certificates were not edited. Each log records its command and exit status. The additional generated Lean source comparison is a text-equality check, not formal proof verification.

The required order-14, general-witness, rectangle, independent rectangle, symbolic, and structural checks passed. Both the independent full order-15 central-cone regeneration and the general full regeneration at orders 14 and 15 passed. The preceding timeout is historical; see `../archived_packaging_logs/`.

The original packaging environment did not have Lean/Lake available; that historical environment limitation is preserved in `lean_build_status_packaging_original.json`. A later final validation rebuilt the complete `Bridge.Young` proof chain successfully under the pinned Lean 4.19.0/mathlib versions. Its scope and trust-boundary checks are summarized in `lean_final_validation_summary.md`, while the packaged Lean source remains `../lieb_4433_lean_round8.zip`.

`headline_arithmetic.py` independently recalculates the stated hook dimensions, partition counts, raw-to-normalized bridge conversion, degree balance, order-15 convex weights, and separator escape arithmetic. It does not replace analytic positivity proofs.

The public historical audit-result checksum discrepancy was only an overwritten elapsed-time field. `historical_result_repair.json` records restoration of the checksum-matching original result from the intact original audit bundle. Both the overwritten previous packaging result and the current fresh result are preserved separately.
