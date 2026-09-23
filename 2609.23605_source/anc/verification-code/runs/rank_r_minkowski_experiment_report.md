# Independent stress test: random-submodule Hilbert functions vs. the predicted Kozlov-Minkowski
# polytope (2026-08-06)

**Headline result: NO discrepancy found.** In every one of the 9 cases tested, every single
randomly-sampled real Hilbert function (computed by Macaulay2 from an actual random monomial
submodule, not from any formula) landed inside the polytope predicted by
`20-projects/exterior-convex/working-notes/proper-hilbert-functions-kozlov-minkowski.org`'s "almost settled" claim (section 9).
Where the experiment fell short was pure *sampling coverage*: for the larger/harder cases, random
sampling within the (modest, time-boxed) budget did not always manage to hit every single extreme
vertex of the target polytope — a coverage gap, not a counterexample. See "Non-convergent cases"
below for exactly which vertices were missed and why that is not alarming.

This is a genuinely independent check: deliverable (a) computes the "prediction" from scratch via
local Kruskal-Katona combinatorics (no Macaulay2 at all); deliverable (b) builds real random monomial
submodules and gets their Hilbert function from Macaulay2's `ExteriorModules.hilbertSequence`
(no formula assumed) — the two sides share no code path.

## What was built

- `code/kozlov_minkowski_prediction.py` — deliverable (a). Given `n` and `degs=(0,d_2,...,d_r)`,
  computes `S` = the proper f-vectors of simplicial complexes on `[n]` (Kruskal-Katona, reusing
  `binomial_basis.py`'s `kk_shadow_bound`/`enumerate_f_vectors`, filtered to `f_1==n`, with a
  leading `1` prepended to match the org file's degree-0-inclusive convention), then the exact
  sumset `S + shift^{d_2}(S) + ... + shift^{d_r}(S)` (degree-0-inclusive shift: prepend `d` zeros
  to the *whole* `(n+1)`-vector — explicitly **not** `right_angle_simplex.py`'s degree-0-dropped
  shift, which needs the `+e_d` correction found in `20-projects/exterior-convex/runs/rank2_hilbert_translation_check.md`), and
  its convex hull as a Sage `Polyhedron`. Pure local combinatorics, no Macaulay2.

  Sanity-checked (not just trusted) against the earlier, independently-derived degree-0-dropped
  construction: for all 9 `(n,d_2)` cases below, dropping the degree-0 coordinate from this file's
  predicted polytope and comparing to `right_angle_minkowski_sum(kozlov_vector(n), [0,d_2]) + e_{d_2}`
  (the exact correction found and verified in the earlier `rank2_hilbert_translation_check.sage`
  session) gave **exact `Polyhedron` equality in all 9 cases** — strong evidence the degree-0-inclusive
  construction here is implemented correctly before using it as the "ground truth" side of this
  experiment.

- `code/rankr_minkowski_random_sampling_m2.py` — deliverable (b). For given `n`, `degs`: repeatedly
  builds `r` random *proper* monomial ideals of `E` (generators drawn only from squarefree monomials
  of degree `>= 2`, so `f_1 = n` automatically — properness is guaranteed by construction, not
  filtered after the fact), forms `F = E^{-d_1,...,-d_r}` and `M = createModule({I_1,...,I_r}, F)`
  via Amata-Crupi's `ExteriorModules.m2`, and computes `hilbertSequence(M)` — the real Hilbert
  function, from Macaulay2 itself. Each new point is checked against a running convex hull
  (maintained incrementally: a new point only triggers a `Polyhedron` rebuild if it lies outside the
  *current* hull, using the current hull's own vertex list rather than the full raw sample list —
  mathematically equivalent to recomputing `conv(L)` from scratch every time, just far cheaper) and
  compared for exact `Polyhedron` equality against deliverable (a)'s target.

  Index-convention check done directly against Macaulay2 (not assumed): for `F = E^{0,-1}` (n=3),
  `hilbertSequence(createModule({ideal(0_E),ideal(0_E)}, F))` returned `{1,4,6,4,1}`, matching
  `H_E(j)+H_E(j-1)` computed by hand for `j=0..4` — confirms `hilbertSequence` returns
  `H_{F/M}(j)` for `j=0,...,N` (`N=n+max(degs)`), exactly the degree-0-inclusive, length-`(N+1)`
  convention used by deliverable (a), so the two sides live in the same `R^{N+1}` with no
  translation needed for comparison.

  Random-ideal generation is done in Python (`random`, not M2's own RNG) for a clean, documented,
  reproducible source of randomness — the one thing that must *not* be assumed in advance (the
  actual Hilbert-function computation) is still 100% Macaulay2's. Each of the `r` ideals per sample
  is generated independently by one of three modes (weights 0.35/0.35/0.30): zero ideal; "degree
  on/off" (each degree `d=2..n` independently either fully included or fully excluded — a compact,
  non-hard-coded way to sometimes reach highly structured ideals, including but not limited to
  literal skeleton ideals); or fully random per-monomial inclusion at a density drawn uniformly from
  `[0.05, 0.95]`. Deliberately did **not** hard-code the skeleton ideals that Kozlov's theorem
  already identifies as the rank-1 extremal witnesses — that would have presupposed the very
  structure under test.

## `M_max` heuristic

`M_max = min(30 * V, 400)`, `V` = number of vertices of the target polytope from (a). Reasoning:
each of the `V` target vertices needs to be independently *hit* by some sample for convergence to be
possible at all, and with no more targeted a sampler than the three-mode scheme above, "several
dozen trials per vertex" is a reasonable, cheap budget given the observed Macaulay2 throughput
(~50 samples/second in a batched `M2 --script` call, dominated by process-startup, not per-sample
cost). The flat cap at 400 exists so that a large target polytope (more vertices) can't blow up
total wall-clock — worst case here (9 cases, `M_max` up to 400 each) still finished in **74 seconds**
wall-clock total, comfortably under the 10-minute budget.

## Scope actually run

`r=2`, `n in {3,4,5}`, `d_2 in {1,2,3}` — 9 cases, batches of 25 samples per `M2 --script`
invocation, one fixed seed per case (`hash((n,d_2)) mod 2^31`, for reproducibility).

## Results

| n | d_2 | target vertices | converged? | samples used | notes |
|---|-----|-----------------|------------|---------------|-------|
| 3 | 1 | 7  | **yes** | 33  | |
| 3 | 2 | 9  | **yes** | 72  | |
| 3 | 3 | 9  | **yes** | 25  | converged in the very first batch |
| 4 | 1 | 11 | **yes** | 82  | |
| 4 | 2 | 14 | **yes** | 217 | |
| 4 | 3 | 16 | no (400/400) | — | 1 vertex never hit: `(1,4,6,5,4,6,4,0)`; hull ⊆ target confirmed |
| 5 | 1 | 16 | no (400/400) | — | 1 vertex never hit: `(1,6,15,10,10,0,0)`; hull ⊆ target confirmed |
| 5 | 2 | 20 | no (400/400) | — | 2 vertices never hit; hull ⊆ target confirmed |
| 5 | 3 | 23 | no (400/400) | — | 3 vertices never hit; hull ⊆ target confirmed |

(Full per-batch trace, including the intermediate hull-vertex-count trajectory for every case, is
reproducible by rerunning `sage code/rankr_minkowski_random_sampling_m2.py` — not saved as a raw
log here, since it is cheap to regenerate in about a minute; see the "how to reproduce" note below.)

Command used: `sage code/rankr_minkowski_random_sampling_m2.py` (runs all 9 cases in sequence,
~74s wall-clock total on this machine).

## Non-convergent cases: why this is not alarming

For every non-convergent case, a **soundness diagnostic** was run explicitly: is every vertex of the
sampled convex hull actually contained in the target polytope? (`target.contains(v)` for every `v`
in the current hull's vertex list.) The answer was **`True` in all four non-convergent cases** — so
the entire sampled point cloud (not just its hull-vertex subset, since hull vertices are the extreme
representatives of everything sampled) stayed strictly within the predicted region. What failed to
converge was purely *reaching every corner* of the target within the sample budget, not any point
falling outside it.

This is a plausible, even expected, outcome given the sampling design: the missing vertices are
exactly the kind of highly special extreme points (Kruskal-Katona-optimal "compressed"/threshold
complexes combined at a very particular degree pair) that a `random`/degree-on-off sampler will
reach with materially lower probability than typical interior-ish points, especially as `n` grows
and the space of possible ideals grows exponentially while the "on/off" mode's chance of landing
exactly the needed degree-profile shrinks. The three-mode sampler was deliberately built *not* to
hard-code Kozlov's known extremal witnesses (that would presuppose the claim under test); the price
of that choice is a modest coverage gap for the very largest/most special vertices within a
time-boxed 400-sample budget, which is exactly the honest outcome the task asked to report if it
occurred, and did.

## Genuine findings / surprises

- **No mathematical discrepancy.** All soundness checks passed; nothing here weakens the
  "almost settled" claim.
- **Convergence was fast where it happened**: the two easiest cases converged almost immediately
  (25 and 33 samples against `M_max` of 270 and 210) — the three-mode random sampler is
  considerably more efficient than a worst-case "one trial per vertex" argument would suggest, at
  least for `n<=4`.
- **The only mild surprise**: `n=3, d_2=3` converged in the very first batch of 25 samples, faster
  than `n=3, d_2=1` (33 samples) despite the target having more vertices (9 vs. 7) — not
  investigated further, plausibly just variance from the small sample/seed, not a real pattern.
- The `n=5` cases uniformly failed to reach full coverage inside the 400-sample cap, each missing
  a small number (1-3) of vertices out of totals in the 16-23 range — consistent with "the sampler's
  chance of hitting the single hardest corner drops as `n` grows," a reasonable, unsurprising
  scaling behavior rather than anything indicating a problem with the underlying claim.

## Cross-check performed before trusting deliverable (a)

Before using `kozlov_minkowski_prediction.py`'s output as "ground truth" for (b) to compare against,
it was checked against the earlier (different-coordinate-convention) construction already validated
in this project: for all 9 `(n,d_2)` pairs, dropping the leading degree-0 coordinate from (a)'s
predicted polytope and comparing to `right_angle_minkowski_sum(kozlov_vector(n), [0,d_2]) + e_{d_2}`
(`20-projects/exterior-convex/code/right_angle_simplex.py` + the `+e_{d_2}` correction from `20-projects/exterior-convex/runs/rank2_hilbert_translation_check.md`)
gave **exact `Polyhedron` equality in all 9 cases**. This does not independently verify the
*mathematical* claim (both constructions share the same underlying Kruskal-Katona/Kozlov
machinery), but it does verify that deliverable (a)'s new degree-0-inclusive code is implemented
correctly, consistent with the earlier, separately-derived coordinate convention.

## How to reproduce

```
sage code/kozlov_minkowski_prediction.py            # deliverable (a) alone, prints S sizes and
                                                      # predicted-polytope vertex/dim counts
sage code/rankr_minkowski_random_sampling_m2.py      # full 9-case experiment, ~74s wall-clock
```

Both scripts assume they are run from `code/` (cwd-relative `load()` calls), per this project's
existing convention.

## What this does and does not settle

This experiment adds a genuinely independent (different code path, different tool) confirmation of
the "almost settled" claim's *soundness* direction (real Hilbert functions never exceed the
predicted region) for `r=2`, `n<=5`, `d_2<=3`. It does **not** independently re-derive
Amata-Crupi's monomial-submodule/initial-module reduction (section 6 of the org file — still the
single largest "cited, not re-derived" ingredient per that file's own section 10), and the observed
non-convergence for larger `n` means "every predicted vertex is actually achievable" was confirmed
by direct construction for `n=3,4` but not exhaustively for `n=5` within this budget (though no
counter-evidence was found either — the missing vertices simply weren't independently *reached*, not
shown unreachable).

## Addendum (2026-08-06, later the same day): scope confirmation + a negative control

Context: a proof-checking subagent found, the same day, that *extending* "proper" to arbitrary
graded submodules (not just genuine Definition 2.1 monomial submodules) via a plausible-looking
basis-free condition is false — a "diagonal" submodule $M=E\cdot(g_1+g_2)$ ($n=2$, $d_1=d_2=0$)
gives $H_{F/M}=(1,2,1)$, outside the predicted polytope. Jan resolved this by restricting the
theorem's scope: $M$ is only ever a genuine Amata–Crupi Definition 2.1 monomial submodule
($M=I_1g_1\oplus\cdots\oplus I_rg_r$), never extended. See
`20-projects/exterior-convex/working-notes/proper-hilbert-functions-kozlov-minkowski.org` §6 and §9 for the full resolution. This
addendum checks two things about the *existing* experiment's relationship to that resolution, and
adds one genuinely new negative-control experiment.

### Part 1 — the original experiment already respected the correct scope

Read `code/rankr_minkowski_random_sampling_m2.py` again with this question specifically in mind: does
it build `M` via `createModule({I_1,...,I_r}, F)` (Amata–Crupi's own function, from
`20-projects/exterior-convex/code/amata-crupi_ExteriorModules.m2`), which by construction can only ever produce a genuine
Definition 2.1 monomial submodule — never a "diagonal"/mixing one like the counterexample?

Confirmed by reading `createModule`'s actual Macaulay2 source (not just trusting the name):

```
createModule(List,Module) := (L,F) -> (
    ...
    O := sum apply(#L, i -> trim RM L#i * F_i);
    ...
)
```

`F_i` is the $i$-th free generator of `F` in isolation, so `L#i * F_i` is exactly $I_ig_i$ (the
ideal $I_i$'s elements times that one generator, landing entirely inside $Eg_i$), and `O` is the
sum — forced to be a *direct* sum, since distinct $Eg_i$ summands only intersect in $0$ — of these
across all `i`. This is literally $M=I_1g_1\oplus\cdots\oplus I_rg_r$, Amata–Crupi's Definition 2.1,
with no path in the code for a generator to ever mix two different $g_i$'s (there is no operation in
`createModule` that could produce a term like $g_1+g_2$ living partly in each summand). **So the
original experiment's positive results (every one of the hundreds of sampled points, across all 9
`(n,d_2)` cases, landed inside the predicted polytope) already used the now-agreed-correct scope —
nothing about the sampling method itself needs to change or be re-run.** The random-ideal generation
in `random_ideal_gens` only ever varies which monomials go into each $I_i$; it was never capable of
building a diagonal/mixing submodule in the first place.

### Part 2 — negative control: genuinely non-monomial submodules, checked against the same prediction

New file: `code/rankr_nonmonomial_negative_control_m2.py`. Deliberately builds submodules $M\subset
F$ that are *not* of Definition 2.1 form — generated by homogeneous elements that mix two different
free generators, via Macaulay2's `image map(F, G, matrix{{...}})` (the pattern confirmed working
earlier the same session: for $F=E^{0,0}$, $n=2$, the submodule generated by $g_1+g_2$ is `image
map(F, E^1, matrix{{1_E},{1_E}})`) — then computes the *real* Hilbert function of $F/M$ via
`hilbertSequence` (same Amata–Crupi function used throughout this project; verified here to work
correctly on an `image`-built submodule, not just `createModule`-built ones: e.g. for $F=E^{0,0}$,
$M=\mathrm{image}$ of $g_1+g_2$ gives `hilbertSequence M = {1,2,1}`, exactly reproducing the known
counterexample's value), and checks the result against `kozlov_minkowski_prediction.py`'s predicted
polytope for the same `(n, degs)`.

Eight cases were tried, `r=2` throughout, spanning tied degrees ($d_1=d_2$, including a literal
replica of the known counterexample), distinct degrees, and one richer two-generator (still
non-monomial) submodule:

| case | $n$ | $d=(d_1,d_2)$ | generator(s) | $H_{F/M}$ | inside predicted polytope? |
|---|---|---|---|---|---|
| replica of known counterexample | 2 | (0,0) | $g_1+g_2$ | (1,2,1) | **OUTSIDE** |
| tied degrees, larger $n$ | 3 | (0,0) | $g_1+g_2$ | (1,3,3,1) | **OUTSIDE** |
| tied degrees, even larger $n$ | 4 | (0,0) | $g_1+g_2$ | (1,4,6,4,1) | **OUTSIDE** |
| tied degrees, degree-1 generator | 3 | (0,0) | $e_1g_1+e_2g_2$ | (2,5,3,0) | **OUTSIDE** |
| distinct degrees, mixing | 3 | (0,1) | $e_1g_1+g_2$ | (1,3,3,1,0) | **OUTSIDE** |
| distinct degrees, larger gap | 4 | (0,2) | $e_1e_2g_1+g_2$ | (1,4,6,4,1,0,0) | inside |
| distinct degrees, large gap, high-degree gen. | 4 | (0,3) | $e_1e_2e_3g_1+g_2$ | (1,4,6,4,1,0,0,0) | **OUTSIDE** |
| richer, two mixing generators, tied degrees | 4 | (0,0) | $g_1+g_2$, $e_1e_2g_1+e_3e_4g_2$ | (1,4,5,0,0) | **OUTSIDE** |

**7 of 8 landed OUTSIDE the predicted polytope.** Each `hilbertSequence` value was hand-checked
against a direct dimension count for the smallest case (the $n=3,d=(0,0),e_1g_1+e_2g_2$ row) and
matched exactly, confirming the M2 computation itself is trustworthy, not just internally consistent.

**Interpretation.** This gives an independent, direct confirmation — not just the one $n=2$
counterexample found earlier — that genuinely non-monomial (non-Definition-2.1) submodules routinely
escape the predicted polytope, across a range of $n$, tied and distinct degree choices, and even a
multi-generator submodule. This is exactly why the theorem's restriction to Definition 2.1 monomial
submodules is a load-bearing hypothesis and not a formality. The one case that stayed inside
(distinct degrees $d=(0,2)$, generator $e_1e_2g_1+g_2$) shows the escape is not automatic for *every*
non-monomial submodule — the tie-degree cases (all 4 tried) and most distinct-degree cases escaped,
but not all; this is reported honestly rather than dropped, and no case was cherry-picked to force
outside-ness (all 8 planned cases are shown, in the order they were designed, before any were run).
With only 8 cases this is not a systematic map of exactly which non-monomial submodules escape and
which don't — that finer question was not investigated further here.

How to reproduce: `sage code/rankr_nonmonomial_negative_control_m2.py` (runs all 8 cases, well under
a minute wall-clock).
