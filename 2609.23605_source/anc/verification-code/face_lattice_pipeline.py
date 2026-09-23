# Changelog (reverse chronological):
# 2026-07-31 17:08 - Claude-Code (agent-shell, no web session): removed the
#   OOM crash's root cause. What actually happened (confirmed via
#   `journalctl -k` and reproduced in isolation -- see LOGBOOK.md): the
#   original `stage2_watcher`/`stage3_watcher` were single long-lived Sage
#   processes looping over ALL jobs in one address space; Sage's internal
#   caches never freed between jobs, so memory climbed monotonically across
#   the 54-job batch and the kernel OOM-killer eventually killed that one
#   process at 15.6GB RSS -- which then dragged the whole terminal (bash,
#   Claude Code, everything sharing its systemd scope) down with it via
#   `systemd`'s cgroup-wide "Stopping timed out, killing" cascade. Measured
#   in isolation afterward: a SINGLE job's peak RSS is actually modest even
#   at the largest case so far (n=8,d=7: ~800MB for stage 2's
#   face_lattice()) -- the crash was accumulation, not any one job being
#   inherently huge. Separately found and fixed a second, sharper bug:
#   `LatticePoset(..., check=True)` (the implicit default stage 3 was
#   using) eagerly computes a dense O(N^2) join_matix() during
#   *construction*, outside `_time_limited`'s try/except entirely -- at
#   N=65026 (n=8,d=7's element count) this is a MemoryError that crashed
#   the whole stage-3 subprocess uncaught. Since these posets are already
#   known-good lattices (reconstructed from Polyhedron.face_lattice()'s own
#   cover relations), added check=False, which defers join/meet computation
#   to only the specific properties that need it lazily -- where it's
#   already safely inside _time_limited's broad except, so an individual
#   property hitting the same O(N^2) wall now degrades to one "not computed
#   (error: MemoryError...)" entry instead of losing the whole job.
#
#   Replaced the two watchers with per-job sentinel-writing entry points
#   (stage{1,2,3}_run_one_job) meant to be invoked one-per-OS-process by the
#   new code/pipeline_orchestrator.py, which runs each job fully isolated
#   (its own systemd --user --scope with a hard MemoryMax/MemorySwapMax
#   ceiling, plus a `ulimit -v` backstop inside it, plus a wall-clock
#   `timeout`) and bounds *aggregate* concurrency across the whole batch --
#   the other latent bug in the original run: 54 stage-1 jobs were launched
#   simultaneously, each individually ulimited but with no cap on their
#   sum. See pipeline_orchestrator.py's own docstring and LOGBOOK.md
#   2026-07-31 for the full writeup, including the actual measured numbers
#   behind the new memory ceilings.
#
# 2026-07-31 - Claude: created this file. Three-stage file-based pipeline
#   for face-lattice statistics, replacing the single-shot
#   face_lattice_stats.py approach for the larger batch Jan wants to run
#   (n>=3, stopping before infeasible -- growth reconnaissance showed total
#   face count grows ~4x per unit n at the worst d, and face_lattice()
#   construction time scales roughly linearly in face count, ~1ms/face,
#   measured up to 24k faces / 23.5s before a 90s timeout was hit at ~89k
#   faces -- see LOGBOOK.md 2026-07-31 for the full numbers).
#
#   Stage 1 (stage1_job): build the polytope, serialize V-repr + H-repr +
#   cheap properties to a "_polytopeonly.json" file. Cheap/fast at every
#   size tested so far (well under a second even at n=12).
#   Stage 2 (stage2_watcher): poll for completed "_polytopeonly.json"
#   files, reconstruct the polytope from its stored V-repr (NOT recomputing
#   the Minkowski sum -- though timing data shows that step was never the
#   bottleneck; this is about clean separation/resumability, not raw
#   speed, per Jan's explicit request), compute face_lattice() (the actual
#   expensive step), and serialize the poset -- as element
#   dimension + vertex-index-set pairs (so poset elements can be matched
#   back to actual faces of the polytope, not just recovered up to
#   isomorphism -- Jan's explicit requirement) plus cover relations -- to a
#   "_polytope-and-flattice.json" file.
#   Stage 3 (stage3_watcher): poll for completed
#   "_polytope-and-flattice.json" files, reconstruct a LatticePoset from
#   the stored cover relations alone, and run the is_*/height/width
#   battery, updating the same file in place. Reconstructing via
#   LatticePoset(cover_relations) rather than using
#   Polyhedron.face_lattice()'s own poset object directly turns out to
#   fix the is_distributive() bug hit in face_lattice_stats.py (that
#   bug is specific to the Polyhedron-native construction) -- confirmed
#   isomorphic to the original face lattice and is_distributive() works,
#   so it's included here despite being excluded there.
#
#   Vertex order is NOT preserved by Polyhedron(vertices=...) reconstruction
#   (confirmed empirically -- Sage's backend reorders), so stage 2 builds an
#   explicit coordinate-based index map from the reconstructed polytope's
#   own vertex order back to stage 1's stored order, and translates every
#   face's ambient_V_indices() through that map before serializing.

"""
Three-stage file-based pipeline for face-lattice statistics of
R = angle(a) + shift^d(angle(a)), a in {ones, kozlov}.

Each (stage, job) unit of work is meant to run as its OWN short-lived OS
process, launched by code/pipeline_orchestrator.py (a plain-Python script,
no Sage import, that does the process management/scheduling and shells out
to `sage -c` per job) -- NOT as one long-lived process handling many jobs.
See that file's docstring and this file's changelog above for why: an
earlier version had stage 2/3 as long-lived "watcher" processes, which
accumulated memory across jobs in one address space and eventually took
the whole terminal down via an OOM cascade.

This module only provides the stage functions themselves -- stage1_job,
stage2_process_one, stage3_process_one do the actual Sage work for one job;
stage{1,2,3}_run_one_job wrap those with a ".started" sentinel file so
external status checks (a human running `ls`, or a fresh orchestrator/agent
after a crash) can distinguish "not started" / "started, still running" /
"started, process gone, no output -- crashed" without needing to inspect
live processes or trust any in-memory state.

Usage (normally invoked by pipeline_orchestrator.py, not by hand):

    sage -c "load('face_lattice_pipeline.py'); stage1_run_one_job(3, 1, 'ones')"
    sage -c "load('face_lattice_pipeline.py'); stage2_run_one_job(3, 1, 'ones')"
    sage -c "load('face_lattice_pipeline.py'); stage3_run_one_job(3, 1, 'ones')"
"""

import json
import os
import time

load('face_lattice_stats.py')  # noqa -- brings in _time_limited, right_angle_simplex.py's
                                # functions, and (unused here) FACE_LATTICE_PROPERTIES


# Stage 3's property battery. Unlike face_lattice_stats.py, is_distributive
# IS included here -- see the changelog comment above for why the bug
# doesn't reproduce on a LatticePoset reconstructed from cover relations.
# Order dimension remains excluded (NP-hard in general, too slow at scale).
POSET_PROPERTIES = [
    'is_graded',
    'is_ranked',
    'is_eulerian',
    'is_modular',
    'is_distributive',
    'is_complemented',
    'is_atomic',
    'is_coatomic',
    'is_self_dual',
    'is_semidistributive',
    'is_join_semidistributive',
    'is_meet_semidistributive',
    'is_upper_semimodular',
    'is_lower_semimodular',
    'is_supersolvable',
    'is_planar',
]


def _atomic_write_json(path, data):
    """
    Write data as indented JSON to path, atomically: write to path + '.tmp'
    then os.rename over the final name (rename is atomic on POSIX, same
    filesystem), so a watcher polling for path's existence never observes
    a half-written file.
    """
    tmp_path = path + '.tmp'
    with open(tmp_path, 'w') as f:
        json.dump(data, f, indent=2)
        f.write('\n')
    os.rename(tmp_path, path)


def _job_basename(n, d, a_name):
    return f'n{n}_d{d}_{a_name}'


def _polytopeonly_path(n, d, a_name, outdir):
    return os.path.join(outdir, _job_basename(n, d, a_name) + '_polytopeonly.json')


def _flattice_path(n, d, a_name, outdir):
    return os.path.join(outdir, _job_basename(n, d, a_name) + '_polytope-and-flattice.json')


def _started_path(stage, n, d, a_name, outdir):
    return os.path.join(outdir, _job_basename(n, d, a_name) + f'_stage{stage}.started')


def _write_started(stage, n, d, a_name, outdir):
    """
    Write a small ".started" sentinel, the FIRST thing a per-job subprocess
    does, before any Sage computation. Deliberately separate from the
    (possibly large) output file -- lets external status checks tell "not
    started" / "started, still running" / "started, no output, process
    gone (crashed/killed)" apart from just the existence of the real
    output file, without inspecting live processes.
    """
    os.makedirs(outdir, exist_ok=True)
    path = _started_path(stage, n, d, a_name, outdir)
    with open(path, 'w') as f:
        json.dump({'pid': os.getpid(), 'started_at': time.time()}, f)


# ---------------------------------------------------------------------------
# Stage 1: polytope construction (V-repr, H-repr, cheap properties)
# ---------------------------------------------------------------------------

def stage1_job(n, d, a_name, outdir='../runs'):
    """
    Build R = angle(a) + shift^d(angle(a)) and serialize its V-representation,
    H-representation, and cheap/fast properties to
    ../runs/n{n}_d{d}_{a_name}_polytopeonly.json.
    """
    os.makedirs(outdir, exist_ok=True)
    a = ones_vector(n) if a_name == 'ones' else kozlov_vector(n)

    t0 = time.time()
    R = right_angle_minkowski_sum(a, [0, d])
    vertices = [[int(x) for x in v] for v in R.vertices_list()]
    equations = [[int(x) for x in eq] for eq in R.equations_list()]
    inequalities = [[int(x) for x in ieq] for ieq in R.inequalities_list()]
    f_vector = [int(x) for x in R.f_vector()]
    t_construct = time.time() - t0

    data = {
        '_description': (
            f'Stage 1 (polytope only) for R = angle(a) + shift^{d}(angle(a)), '
            f'n={n}, d={d}, a={a_name}. V-representation, H-representation, and '
            f'cheap/fast properties only -- no face lattice yet. Generated by '
            f'code/face_lattice_pipeline.py:stage1_job. See ../runs/description.md.'
        ),
        'stage': 1,
        'n': int(n),
        'd': int(d),
        'a_name': a_name,
        'a': [int(x) for x in a],
        'vertices': vertices,
        'equations': equations,
        'inequalities': inequalities,
        'dim': int(R.dim()),
        'ambient_dim': int(R.ambient_dim()),
        'f_vector': f_vector,
        'n_vertices': len(vertices),
        'n_facets': int(R.n_facets()),
        'total_faces': int(sum(f_vector)),
        'timing': {
            # NB: plain round() is shadowed by Sage's own round() in this
            # namespace (load()-ed code shares globals with the calling
            # Sage session), which returns a non-JSON-serializable RDF
            # element rather than a Python float -- see
            # face_lattice_stats.py for where this was first hit.
            'construct_polytope_seconds': float(round(t_construct, 4)),
        },
        'wall_clock_seconds': float(round(time.time() - t0, 4)),
    }
    path = _polytopeonly_path(n, d, a_name, outdir)
    _atomic_write_json(path, data)
    return path


def stage1_batch(jobs, outdir='../runs'):
    """jobs: list of (n, d, a_name) tuples. Runs them sequentially in this process."""
    return [stage1_job(n, d, a_name, outdir) for n, d, a_name in jobs]


def stage1_run_one_job(n, d, a_name, outdir='../runs'):
    """
    Entry point for pipeline_orchestrator.py: write the ".started" sentinel,
    then run stage 1 for exactly this one job. Meant to be the whole
    workload of one short-lived OS process (see module docstring).
    """
    _write_started(1, n, d, a_name, outdir)
    return stage1_job(n, d, a_name, outdir)


# ---------------------------------------------------------------------------
# Stage 2: face lattice construction from stored V-repr
# ---------------------------------------------------------------------------

def _reconstruct_polytope_and_index_map(stage1_data):
    """
    Rebuild the Polyhedron from stage1_data['vertices'], and return
    (R2, index_map) where index_map[j] gives the index into stage1_data's
    ORIGINAL vertex list for the j-th vertex of the reconstructed polytope
    R2 -- needed because Polyhedron(vertices=...) does not preserve input
    order (confirmed empirically; the backend re-sorts).
    """
    stored_vertices = stage1_data['vertices']
    R2 = Polyhedron(vertices=stored_vertices)
    stored_lookup = {tuple(v): i for i, v in enumerate(stored_vertices)}
    index_map = {j: stored_lookup[tuple(v)] for j, v in enumerate(R2.vertices_list())}
    return R2, index_map


def stage2_process_one(n, d, a_name, outdir='../runs', face_lattice_timeout=180):
    """
    Read the completed polytopeonly file for (n, d, a_name), reconstruct
    the polytope from its stored V-repr, compute the face lattice, and
    write the polytope-and-flattice file. Returns the output path.

    face_lattice() itself is wrapped in a wall-clock timeout (SIGALRM, same
    mechanism as face_lattice_stats.py's per-property timeout) -- at larger
    n this is the one truly expensive, size-dependent step (measured
    roughly linear in face count, ~1ms/face, but a single oversized job
    hanging here would otherwise block this whole watcher process
    indefinitely). On timeout, no 'poset' key is written and
    'face_lattice_status' records why -- stage 3 skips such files rather
    than erroring on a missing 'poset' key.
    """
    in_path = _polytopeonly_path(n, d, a_name, outdir)
    with open(in_path) as f:
        stage1_data = json.load(f)

    t0 = time.time()
    R2, index_map = _reconstruct_polytope_and_index_map(stage1_data)
    t_reconstruct = time.time() - t0

    data = dict(stage1_data)  # carry stage 1's fields forward
    data['stage'] = 2
    data['timing']['reconstruct_polytope_seconds'] = float(round(t_reconstruct, 4))

    ok, val = _time_limited(R2.face_lattice, face_lattice_timeout)
    if not ok:
        data['_description'] = (
            f'Stage 2 (polytope + face lattice attempt) for '
            f'R = angle(a) + shift^{d}(angle(a)), n={n}, d={d}, a={a_name}. '
            f'face_lattice() did not complete -- see face_lattice_status. '
            f'No poset data in this file; stage 3 will skip it. Generated by '
            f'code/face_lattice_pipeline.py:stage2_process_one. '
            f'See ../runs/description.md.'
        )
        data['face_lattice_status'] = val
        data['wall_clock_seconds'] = float(round(time.time() - t0, 4))
        out_path = _flattice_path(n, d, a_name, outdir)
        _atomic_write_json(out_path, data)
        return out_path

    FL = val
    t_face_lattice = time.time() - t0 - t_reconstruct

    elements = list(FL)
    element_index = {e: i for i, e in enumerate(elements)}
    elements_serialized = [
        {
            'dim': int(e.dim()),
            # sorted indices into stage 1's ORIGINAL vertex list (self-contained
            # cross-reference: matches poset elements back to actual faces of
            # the polytope, not just recovering the poset up to isomorphism)
            'vertex_indices': sorted(index_map[j] for j in e.ambient_V_indices()),
        }
        for e in elements
    ]
    cover_relations = [
        [element_index[x], element_index[y]] for x, y in FL.cover_relations()
    ]

    data['_description'] = (
        f'Stage 2 (polytope + face lattice) for R = angle(a) + shift^{d}(angle(a)), '
        f'n={n}, d={d}, a={a_name}. Poset serialized as element '
        f'dim/vertex_indices pairs plus cover_relations (index pairs); '
        f'vertex_indices refer back to this same file\'s own "vertices" list, '
        f'so poset elements can be matched to specific faces of the polytope, '
        f'not just recovered up to isomorphism. Generated by '
        f'code/face_lattice_pipeline.py:stage2_process_one. '
        f'See ../runs/description.md.'
    )
    data['poset'] = {
        'elements': elements_serialized,
        'cover_relations': cover_relations,
    }
    data['face_lattice_status'] = 'ok'
    data['timing']['face_lattice_seconds'] = float(round(t_face_lattice, 4))
    data['wall_clock_seconds'] = float(round(time.time() - t0, 4))

    out_path = _flattice_path(n, d, a_name, outdir)
    _atomic_write_json(out_path, data)
    return out_path


def stage2_run_one_job(n, d, a_name, outdir='../runs'):
    """
    Entry point for pipeline_orchestrator.py: write the ".started" sentinel,
    then run stage 2 for exactly this one job. Meant to be the whole
    workload of one short-lived OS process (see module docstring -- this
    replaces the old stage2_watcher, which ran ALL jobs in one long-lived
    process and was the direct cause of the 2026-07-31 OOM crash).
    """
    _write_started(2, n, d, a_name, outdir)
    return stage2_process_one(n, d, a_name, outdir)


# ---------------------------------------------------------------------------
# Stage 3: poset statistics from stored cover relations
# ---------------------------------------------------------------------------

def stage3_process_one(n, d, a_name, outdir='../runs', timeout=30):
    """
    Read the completed polytope-and-flattice file for (n, d, a_name),
    reconstruct a LatticePoset from its stored cover relations alone, run
    the is_*/height/width battery, and update the same file in place with
    the results.

    If stage 2 gave up on face_lattice() (no 'poset' key -- see
    stage2_process_one's face_lattice_timeout), this is a no-op beyond
    recording that fact, rather than a KeyError.
    """
    path = _flattice_path(n, d, a_name, outdir)
    with open(path) as f:
        data = json.load(f)

    if 'poset' not in data:
        data['poset_stats'] = 'not computed (stage 2 has no poset data -- see face_lattice_status)'
        data['stage'] = 3
        _atomic_write_json(path, data)
        return path

    elements = data['poset']['elements']
    cover_relations = [tuple(pair) for pair in data['poset']['cover_relations']]
    N = len(elements)

    t0 = time.time()
    # check=False: skip LatticePoset's default eager join_matrix() validation
    # (O(N^2), computed during CONSTRUCTION itself -- outside _time_limited's
    # try/except, so at N=65026 this was an uncaught MemoryError that took
    # down the whole subprocess -- see the 2026-07-31 changelog entry above).
    # Safe to skip: this poset is already a known-good lattice, reconstructed
    # from Polyhedron.face_lattice()'s own cover relations (confirmed
    # isomorphic, see stage2_process_one). Individual properties below that
    # still need the join/meet table now hit the same O(N^2) wall lazily,
    # but INSIDE _time_limited's broad except -- so it costs one "not
    # computed (error: MemoryError...)" entry, not the whole job.
    LP = LatticePoset((list(range(N)), cover_relations), cover_relations=True, check=False)

    stats = {
        'excluded_properties': {
            'order_dimension': 'NP-hard in general, too slow at this scale',
        },
        'timeout_seconds': int(timeout),
    }
    ok, val = _time_limited(LP.height, timeout)
    stats['height'] = int(val) if ok else val
    ok, val = _time_limited(LP.width, timeout)
    stats['width'] = int(val) if ok else val
    for prop in POSET_PROPERTIES:
        ok, val = _time_limited(getattr(LP, prop), timeout)
        stats[prop] = bool(val) if ok else val

    data['_description'] = (
        f'Stage 3 (poset statistics) for R = angle(a) + shift^{d}(angle(a)), '
        f'n={n}, d={d}, a={a_name}. LatticePoset reconstructed from this '
        f"file's own cover_relations alone (NOT from the polytope directly), "
        f'then the is_*/height/width battery run on it -- including '
        f'is_distributive, which is broken on Polyhedron.face_lattice()\'s '
        f'own poset object (see code/face_lattice_stats.py) but works fine '
        f'here on the reconstructed LatticePoset. Generated by '
        f'code/face_lattice_pipeline.py:stage3_process_one. '
        f'See ../runs/description.md.'
    )
    data['stage'] = 3
    data['poset_stats'] = stats
    data.setdefault('timing', {})['poset_stats_seconds'] = float(round(time.time() - t0, 4))
    data['wall_clock_seconds'] = float(round(
        data.get('wall_clock_seconds', 0) + (time.time() - t0), 4
    ))

    _atomic_write_json(path, data)
    return path


def stage3_run_one_job(n, d, a_name, outdir='../runs', timeout=30):
    """
    Entry point for pipeline_orchestrator.py: write the ".started" sentinel,
    then run stage 3 for exactly this one job. Meant to be the whole
    workload of one short-lived OS process (see module docstring -- this
    replaces the old stage3_watcher, which ran ALL jobs in one long-lived
    process; combined with the check=True join_matix() bug above, that
    watcher is what actually got OOM-killed on 2026-07-31).
    """
    _write_started(3, n, d, a_name, outdir)
    return stage3_process_one(n, d, a_name, outdir, timeout)
