# runs/ — face-lattice statistics logs

Machine-generated JSON logs of Sage face-lattice statistics for R = angle(a) + shift^d(angle(a)),
for a = all-ones or a = Kozlov vector. Two generations of this directory now coexist (different
filenames, no collision) — see below.

## Generation 2 (2026-07-31): three-stage pipeline, `20-projects/exterior-convex/code/face_lattice_pipeline.py` +
`20-projects/exterior-convex/code/pipeline_orchestrator.py`

Built to support pushing to larger n without losing partial work or risking one hung/oversized job
taking others down with it. Three separate stages, communicating via files in this directory
(atomic write: `.tmp` then `rename`, so anything polling for a file's existence never sees a
half-written one):

- **Stage 1** (`stage1_job`): builds R, writes V-representation, H-representation, and cheap/fast
  properties (dim, f-vector, vertex/facet counts) to `n{n}_d{d}_{a_name}_polytopeonly.json`.
- **Stage 2** (`stage2_process_one`): reconstructs the polytope from its *stored* V-repr
  (deliberately not recomputing the Minkowski sum, per Jan's explicit request, even though timing
  data shows that step was never the actual bottleneck — this is about clean stage
  separation/resumability, not speed), computes the face lattice, and writes
  `n{n}_d{d}_{a_name}_polytope-and-flattice.json`. The poset is serialized as element `dim` +
  `vertex_indices` (indices into this same file's own `vertices` list, carried forward from stage 1)
  plus `cover_relations` (index pairs) — enough to reconstruct the poset *and* to match each poset
  element back to the specific face of the polytope it came from, not just recover the poset up to
  isomorphism (Jan's explicit requirement; vertex order is NOT preserved by
  `Polyhedron(vertices=...)` reconstruction — confirmed empirically — so stage 2 builds an explicit
  coordinate-based index map to translate `ambient_V_indices()` back to stage 1's original order).
- **Stage 3** (`stage3_process_one`): reconstructs a `LatticePoset` from the stored
  `cover_relations` *alone* (not from the polytope), runs the `is_*`/height/width battery, and
  updates the same file in place with a `poset_stats` field. Uses `LatticePoset(..., check=False)`
  (as of the 2026-07-31 17:21 fix — see exterior-convex/LOGBOOK/) rather than the implicit `check=True` default,
  since the latter eagerly builds an O(N^2) `join_matrix()` *during construction*, outside the
  per-property timeout/exception guard entirely — a real crash at the sizes this pipeline reaches.

**Bonus finding**: reconstructing via `LatticePoset(cover_relations)` rather than using
`Polyhedron.face_lattice()`'s own poset object directly fixes the `is_distributive()` bug from
generation 1 below (confirmed isomorphic to the original face lattice, and `is_distributive()` works
correctly on the reconstruction) — so stage 3 includes it, unlike generation 1's `face_lattice_stats.py`.

**Orchestration (redesigned 2026-07-31 17:21, after an OOM crash — full incident writeup in
exterior-convex/LOGBOOK/)**: each `(stage, job)` unit of work runs as its own short-lived `sage -c` subprocess,
never as a long-lived process handling many jobs — the original design's `stage2_watcher`/
`stage3_watcher` accumulated memory across jobs in one shared address space, which is what actually
got OOM-killed and, via a systemd cgroup-wide teardown, took the whole terminal (and Claude Code)
down with it. `20-projects/exterior-convex/code/pipeline_orchestrator.py` (plain Python, no Sage import) now launches each job
inside its own `systemd-run --user --scope` with a hard `MemoryMax`/`MemorySwapMax` ceiling, a
`ulimit -v` backstop, and a wall-clock `timeout`, all sized from real isolated-job memory
measurements; a single global concurrency cap (5) bounds aggregate memory across every stage
combined. Each job writes a `.started` sentinel file (pid + timestamp) as its first action, before
any Sage computation — replaces the informal "watcher" concept with a concrete, filesystem-visible
status protocol: `not_started` (no sentinel) / `running` (sentinel + live pid) / `done` (expected
output present) / `crashed` (sentinel + dead pid + no output), readable without inspecting any live
process or trusting in-memory state. See `pipeline_orchestrator.py`'s own docstring for the full
design rationale and `20-projects/exterior-convex/LOGBOOK/LOGBOOK-session-03-20260731.md` 2026-07-31 17:21 for the incident this responds to.

Validated (2026-07-31) end-to-end: smoke-tested on small jobs first (confirmed real subprocess
launch + sentinel + isolation + correct output via direct file inspection), then ran the full
remaining stage-3 backfill (44 jobs, n=5..8) as a single orchestrator run — all 54 units of work
(44 new + 10 already-done from the pre-crash run, correctly detected and skipped) finished cleanly,
0 crashed, system memory staying under ~7GB throughout (vs. the ~57GB scope peak that caused the
original crash).

File naming: `n{n}_d{d}_{a_name}_polytopeonly.json`, `n{n}_d{d}_{a_name}_polytope-and-flattice.json`,
and (new) `n{n}_d{d}_{a_name}_stage{1,2,3}.started` / `_stage{1,2,3}.log` per-job status/output
sentinels written by the orchestrator.

## Generation 1 (2026-07-31, superseded by generation 2 above for anything not yet regenerated):
single-shot pipeline, `20-projects/exterior-convex/code/face_lattice_stats.py`

Everything below this point describes the original single-file-per-job approach. Still valid data,
just a different (simpler, non-staged) generation method — kept for the cases not yet redone
through generation 2.

Status (2026-07-31): **complete** — all 10 planned logs generated (n=3,4; d=1,...,n-1; a in
{ones, kozlov}), format approved by Jan after reviewing the initial n=3, d=1 pair. All 10 generated
cleanly: no timeouts, no `"not computed"` entries anywhere.

## File naming

`facelattice_n{n}_d{d}_{a_name}.json`, e.g. `facelattice_n3_d1_ones.json`.

## Format

Human-readable (indented) JSON. Since JSON has no comment syntax, each file's own `_description`
field serves as its header comment (matching this project's usual convention of a timestamped
comment atop code files — see `20-projects/exterior-convex/code/right_angle_simplex.py`'s changelog — adapted here since these
are generated data files, not source).

Fields:

- `n`, `d`, `a_name`, `a` — the parameters R was built from.
- `dim`, `ambient_dim`, `f_vector`, `total_faces` — basic polytope data (same as
  `Polyhedron.f_vector()` etc.).
- `height`, `width` — of the face lattice as a poset.
- A battery of `is_*` structural predicates (graded, ranked, Eulerian, modular, complemented,
  atomic, coatomic, self-dual, semidistributive and its two one-sided variants, upper/lower
  semimodular, supersolvable, planar).
- `excluded_properties` — documents what was deliberately *not* attempted at all (not even with a
  timeout): `is_distributive` (a genuine Sage bug — internally calls `.join_irreducibles()`, which
  raises `AttributeError` on lattices built via `Polyhedron.face_lattice()`, as opposed to
  `Poset`/`LatticePoset` built directly) and order dimension (NP-hard in general; an attempt on the
  n=3, d=1 case ran for minutes with no result and was killed — see `20-projects/exterior-convex/LOGBOOK/LOGBOOK-session-03-20260731.md` 2026-07-31).
- `timeout_seconds` — the per-property wall-clock budget actually used (via `SIGALRM`) for
  everything that *was* attempted.
- Any property that timed out or raised an exception is recorded as a string starting
  `"not computed (...)"` instead of `true`/`false`, rather than failing the whole log — so a log
  can be genuinely half-complete and still usable. None of the n=3, d=1 logs needed this fallback;
  it's untested against a real timeout so far.
- `wall_clock_seconds` — total generation time for the log (sanity-check/debugging field).

## Context

This was prompted by a literature check (see `20-projects/exterior-convex/working-notes/right-angle-simplices-notes.md`'s "Is R a
known named polytope?" section) into whether R's face lattice matches a known small poset/lattice.
No usable enumeration database exists at these sizes (26 to 226+ elements — well beyond the ~10-16
element range covered by databases like Ralph Freese's or Jipsen's small-lattice catalogs), so this
directory is Plan B: compute enough structural invariants directly to characterize the face
lattices ourselves, across a range of n and d, rather than looking them up.

Also already known, worth keeping in mind when reading these logs: R's combinatorial type is
**not** independent of the choice of a in general (mismatching f-vectors were found for n=5,6 at
intermediate d back on 2026-07-30, and again for n=4, d=1 while sizing this run matrix — a=ones and
a=kozlov diverge there too), but the two choices happen to coincide exactly at n=3 (both d=1 and
d=2) and at n=4, d=2 and d=3. **n=4, d=1 is the smallest known case where they differ** — confirmed
(2026-07-31) by diffing the two logs directly: the divergence is purely numeric (f_vector, width,
total_faces: 58 vs 66 faces), while every single `is_*` boolean predicate is identical between the
two. So even in the one case in this matrix where the polytopes aren't isomorphic, they still share
the exact same qualitative structural profile — worth keeping in mind if a full characterization of
which invariants are a-independent is ever attempted.
