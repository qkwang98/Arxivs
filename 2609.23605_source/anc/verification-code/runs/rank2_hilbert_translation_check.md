# rank2_hilbert_translation_check.sage (2026-08-06)

Cheap to recompute (a few seconds in Sage) — brief log only, no raw data dump.

Checks the TEXIMG-9 candidate theorem from `../../transcripts/session-images-2026-08-06-1156.org`
(the claim that $R=\angle(a)+\mathrm{shift}^d(\angle(a))$, $a=$ Kozlov vector, equals the convex
hull of achievable rank-2 Hilbert functions of $F=Eg_1\oplus Eg_2$, $\deg g_2=d$) against $n=6$,
$d=1,\ldots,5$.

Command: `sage code/rank2_hilbert_translation_check.sage`.

Result: **the original claim ($\mathrm{conv}(\mathcal H_2)=R$ exactly) is false** — confirmed both
numerically here and by hand via a direct monomial-basis count for $n=2,d=1$ (worked in the
session, not saved as code, see the TEXIMG-9 correction for the arithmetic). The correct statement
is
$$\mathrm{conv}(\mathcal H_2(0,d)) = R + e_d$$
($e_d$ = unit vector at ambient coordinate $d$) — the naive vector-sum $h_1+\mathrm{shift}^d(h_2)$
of two rank-1 Hilbert functions is missing exactly "+1" at ambient degree $d$: the surviving
generator $g_2$'s own degree-0 contribution ($H_{E/I_2}(0)=1$), which the geometric shift
(prepend-$d$-zeros) wrongly zeroes out instead of setting to 1.

For every $d=1,\ldots,5$: `C == S_naive` (True — $R$ as already built via `right_angle_simplex.py`
matches the naive vertex-pair-sum construction, as expected/tautological), `C == S_true` (False —
$R$ does *not* equal the corrected/true Hilbert-function polytope), `(C + e_d) == S_true` (True —
confirms the discrepancy is *exactly* the single translation $e_d$, uniformly, not something more
complicated). `C.n_vertices()` = 22, 27, 31, 34, 36 for $d=1,\ldots,5$ — matches the
`n_vertices(kozlov)` column already in `20-projects/exterior-convex/working-notes/right-angle-simplices-notes.md`'s extremal-matrix
table exactly, confirming the script's construction of $R$ itself is correct.

Does not affect the *structural* content of TEXIMG-9 (Kozlov's theorem generalizes to rank $r$ via
$\mathrm{conv}(A+B)=\mathrm{conv}(A)+\mathrm{conv}(B)$) — only the exact statement, which needs an
explicit additive correction. General rank-$r$ conjecture (not yet checked beyond $r=2$): the
correction is $+\sum_{i=2}^r e_{d_i}$ (one unit bump per non-first generator, at its own degree).
