# rankr_hilbert_series_m2.py (2026-08-06)

Cheap to recompute (a few seconds, dominated by M2 process startup) — brief log only.

Command: `python3 code/rankr_hilbert_series_m2.py` (n=3, degs=(0,1)); also tested directly via
`all_hilbert_series(2, (0,1))`.

- $n=2$, degs=$(0,1)$: 20 distinct achievable Hilbert sequences, including $(0,0,0,0)$ (the
  all-zero/$M=F$ case) — **all 20 independently confirmed** by `ExteriorModules.isHilbertSequence`.
  Includes $(1,3,3,1)$, matching the $M=0$ hand-check from the earlier r=2 translation-bug session.
- $n=3$, degs=$(0,1)$: 69 distinct sequences, **all 69 confirmed**.

Both runs: `m2_rank1_hilbert_sequences` dropped exactly one bogus `(-1,0,...,0)` entry from
Macaulay2's own `allHilbertSequences(E)` output before combining — see `../LOGBOOK/`'s
2026-08-06 20:43 entry (two real package bugs found and worked around, flagged in `20-projects/exterior-convex/TODO.md`,
not filed anywhere).

No mismatches found in any run so far (every combinatorially-generated sequence was confirmed by
M2's independent oracle) — good evidence the exact-sumset identity
(`20-projects/exterior-convex/working-notes/right-angle-simplices-notes.md`'s rank-r section) is correct, on top of the earlier
convex-hull-only checks. Not yet run for $r=3$ or larger $n$ (M2 process-startup cost and the
$|{\rm rank1}|^r$ combination blow-up both grow — untested how far this scales).
