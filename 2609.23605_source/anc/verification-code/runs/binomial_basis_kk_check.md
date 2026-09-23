# binomial_basis.py verification run (2026-08-02)

Cheap to recompute (a few seconds in Sage) — brief log only, no raw data dump.

Command: `sage -c "load('binomial_basis.py'); ..."` (see `20-projects/exterior-convex/code/binomial_basis.py`'s
changelog/docstrings for the exact calls).

Results:

- `verify_shift_formula(8)`: closed-form shift^d-in-binomial-basis formula matches direct
  conjugation `T(n)*N^d*S(n)` for all n=2..8, all d=0..n. **PASS.**
- `brute_force_f_vectors(4)` vs `enumerate_f_vectors(4)` (KK-recursion): both give exactly the same
  25 f-vectors for n=4 (brute force over all 2^15 downward-closed families on 4 labeled vertices).
  **MATCH.**
- For n=4 (25 f-vectors), n=5 (95), n=6 (552), every KK-achievable f-vector has:
  - all binomial coordinates >= 0 (density sequence f_j/binom(n,j) non-increasing), and
  - binomial coordinates summing to exactly f_1/n.
  **PASS for all three n.**

See `20-projects/exterior-convex/working-notes/right-angle-simplices-notes.md`'s "Binomial basis of R^n" section for the proofs
(sum fact: linear algebra of T(n); nonnegativity: elementary double-counting) and what remains
open (exact shape of the image, not just these two necessary conditions).
