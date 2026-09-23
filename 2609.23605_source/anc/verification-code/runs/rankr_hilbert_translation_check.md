# rankr_hilbert_translation_check.sage (2026-08-06)

Cheap to recompute (well under a minute in Sage) — brief log only, no raw data dump.

Generalizes `rank2_hilbert_translation_check.sage`'s finding to general rank $r$: checks the
conjectured correction $R+\sum_{i=2}^r e_{d_i}$ against a *directly computed* true-Hilbert-function
polytope (`trueshift`, built from scratch per generator via its own $f_0=1$ bump — not derived from
the naive sum plus an assumed correction, an independent construction).

Command: `sage code/rankr_hilbert_translation_check.sage`.

Three cases, all **confirmed** (`R == S_naive` true/tautological throughout;
`R == S_direct` false throughout — same bug as the r=2 case, at every non-first generator's own
degree; `R + correction == S_direct` true throughout, exact Sage `Polyhedron` equality):

- $n=5$, degs $=(0,1,2)$ ($r=3$, distinct degrees): correction $=e_1+e_2$, 45 vertices both sides.
- $n=5$, degs $=(0,2,2)$ ($r=3$, **tied** degrees $d_2=d_3=2$): correction $=2e_2$ — confirms the
  multiplicity handling (two generators sharing a degree bump that coordinate by 2, not 1).
- $n=4$, degs $=(0,1,1,2)$ ($r=4$, one tie plus one distinct): correction $=2e_1+e_2$.

**Conclusion**: the general-rank correction conjectured in
`20-projects/exterior-convex/working-notes/right-angle-simplices-notes.md`'s rank-2 section,
$$\operatorname{conv}(\mathcal H_r(d_1,\ldots,d_r)) = R + \sum_{i=2}^r e_{d_i},$$
holds in every case tested, including ties. Still not a from-scratch proof for general $n,r$ — the
degree-by-degree argument in the notes is general-purpose and this data has no counterexample, but
it remains a finite computational check ($n\le5$, a handful of $(r,\mathrm{degs})$ choices), not a
theorem.
