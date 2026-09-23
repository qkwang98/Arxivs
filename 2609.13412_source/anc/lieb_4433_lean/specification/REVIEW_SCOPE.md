# Independent review scope

Claim under review:

For every complex Hermitian positive-semidefinite 14 x 14 matrix A,

d_(4,4,3,3)(A) / 12012 <= per(A).

If correct, this closes the previously missing ordinary S_14-immanant case and, together with the cited established cases, gives ordinary-immanant permanental dominance through order 14.

The proof is intended to be logically independent of the earlier discovery rounds. Do not assume any unpublished partial result from those rounds. The only imported mathematical dependency needed for the final corollary is the established Pate coverage theorem for the four right-hand partitions; verify that dependency independently from the cited literature.

Suggested order:
1. Read FINAL_PROOF.md without assuming the conclusion.
2. Audit the universal partial-transpose positivity argument and the passage from the group-algebra witnesses to nonnegative immanant combinations.
3. Audit all normalization factors and the convex-combination bridge inequality.
4. Run `python verify_all.py` inside exact_certificate/ and inspect what it does and does not verify.
5. Independently verify the applicability of the cited Pate theorem to (6,5,3), (6,4,4), (5,5,4), and (5,3,3,3).
6. Classify any issue as fatal, substantive but repairable, minor, or optional. Do not manufacture objections if none survive checking.

The bundled scripts are exact arithmetic checks, not a proof-assistant formalization of the universal analytic argument.
