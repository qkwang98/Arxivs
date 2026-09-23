# Changelog (reverse chronological):
# 2026-08-01 - Claude: switched to Sage-only bulk computation (Julia/Oscar now used only for a
#   spot-check subsample, not full tandem verification of every point) -- per Jan's instruction,
#   after finding Julia/Oscar is ~15x slower per-point here (Polymake.jl#392, "Frequent tiny
#   allocations", a known/acknowledged low-priority perf characteristic of the Julia<->C++/Perl
#   BigObject interop, not a bug). Added run_on_points_chunk (processes a slice of the point list,
#   for parallel workers -- see the new parameter_space_n5d1_parallel.py orchestrator) and
#   merge_chunks_with_spotcheck (combines parallel chunk outputs, cross-references an Oscar
#   spot-check results file, and annotates every point's oscar_f_vector as either the checked
#   value or the literal string "not computed").
# 2026-08-01 - Claude: switched the shared point list and file extension from plain comma-lines
#   to JSON, now that JSON3 (524K, already cached as a transitive Oscar dependency) is registered
#   as a direct dependency of the Julia environment -- Jan asked for "JSON everywhere for runs"
#   once he learned the size wasn't actually a concern. See parameter_space_n5d1.jl and
#   compare_n5d1_tandem.py for the matching changes. Also: write_random_points needed explicit
#   int() casts -- Sage's preparser turns integer literals/random.randint results into Sage
#   Integer objects, which plain json.dump can't serialize.
# 2026-08-01 - Claude: created this file, mirroring parameter_space_n4d1.py's structure and
#   conventions for the n=5, d=1 case -- the natural next step after n=4,d=1's two-type wall
#   a2*a4=a3^2 (see ../LOGBOOK.md's 2026-08-01 entry and Jan's proposed generalization to three
#   GP-style conditions a1*a3=a2^2, a2*a4=a3^2, a3*a5=a4^2). Per Jan's explicit requirement, every
#   experiment here is run in tandem with the Julia/Oscar counterpart (parameter_space_n5d1.jl)
#   against an IDENTICAL shared point list (written by write_random_points), not independent
#   per-language RNG streams -- Sage's and Julia's random number generators aren't comparable
#   even from "the same seed", so a materialized shared point list is the only reliable way to
#   get identical inputs. See compare_n5d1_tandem.py for the diff step.

"""
Exploration of the a=(a1,...,a5) parameter space for n=5, d=1 -- the natural next case after
n=4,d=1 (see parameter_space_n4d1.py, which found exactly two combinatorial types separated by
the wall a2*a4=a3^2). Not part of the main proof pipeline; "fun, not important" per Jan's framing.

Workflow (every experiment run in tandem with parameter_space_n5d1.jl):

    sage -c "load('parameter_space_n5d1.py'); write_random_points(500, 10**6, seed=3)"
    sage -c "load('parameter_space_n5d1.py'); run_on_points('paramspace_n5_d1_points_seed3_N500.json')"
    julia parameter_space_n5d1.jl ../runs/paramspace_n5_d1_points_seed3_N500.json
    python3 compare_n5d1_tandem.py ../runs/paramspace_n5_d1_results_sage_seed3_N500.json \\
                                    ../runs/paramspace_n5_d1_results_julia_seed3_N500.json

Shared point list and both languages' results are all plain JSON (JSON3 is a direct dependency of
this project's Julia environment as of 2026-08-01).
"""

import json
import os
import random
import time

load('right_angle_simplex.py')  # noqa -- brings in right_angle_minkowski_sum

OUTDIR = '../runs'
D = 1  # fixed throughout this file; n=5 is implicit in every a having 5 entries


def _fvector(a):
    R = right_angle_minkowski_sum(list(a), [0, D])
    return tuple(int(x) for x in R.f_vector())


def write_random_points(n_points, maxval, seed=None):
    """
    Uniform random a_i in [1, maxval], n_points samples. Writes ONLY the raw point list (JSON, no
    f-vectors) to ../runs/ -- both this file's run_on_points and the Julia counterpart then
    consume the exact same points.
    """
    if seed is not None:
        random.seed(int(seed))
    n_points, maxval = int(n_points), int(maxval)
    seed = int(seed) if seed is not None else None
    points = [[int(random.randint(1, maxval)) for _ in range(5)] for _ in range(n_points)]
    os.makedirs(OUTDIR, exist_ok=True)
    filename = f'paramspace_n5_d1_points_seed{seed}_N{n_points}.json'
    path = os.path.join(OUTDIR, filename)
    with open(path, 'w') as f:
        json.dump({'n': 5, 'd': D, 'maxval': maxval, 'seed': seed, 'points': points}, f)
    print(f'wrote {path}: {n_points} points')
    return path


def write_spotcheck_points(points_filename, n_spotcheck, seed=None):
    """
    Draws a random subsample of n_spotcheck points from an existing point list and writes it in
    the same points-file format, so the existing (unchanged) Julia/Oscar
    parameter_space_n5d1.jl:run_on_points can process it directly -- this is the "Oscar spot-check"
    half of the Sage-bulk/Oscar-spot-check split.
    """
    n_spotcheck = int(n_spotcheck)
    seed = int(seed) if seed is not None else None
    if seed is not None:
        random.seed(seed)
    with open(os.path.join(OUTDIR, points_filename)) as f:
        data = json.load(f)
    sample = random.sample(data['points'], n_spotcheck)
    out_filename = points_filename.replace('.json', f'_spotcheck_seed{seed}_N{n_spotcheck}.json')
    path = os.path.join(OUTDIR, out_filename)
    with open(path, 'w') as f:
        json.dump({'n': 5, 'd': D, 'spotcheck_of': points_filename, 'seed': seed,
                   'points': sample}, f)
    print(f'wrote {path}: {n_spotcheck} spot-check points')
    return path


def run_on_points(points_filename):
    """
    Reads a shared point list (from write_random_points, or hand-written -- e.g. for targeted
    probes) and computes f-vectors via Sage, writing results to ../runs/ as JSON. Labels each
    point "generic case"/"special case" by comparing against this run's own majority f-vector,
    same data-driven convention as parameter_space_n4d1.py.
    """
    path_in = os.path.join(OUTDIR, points_filename)
    with open(path_in) as f:
        points_in = json.load(f)['points']
    t0 = time.time()
    points = [(tuple(a), _fvector(a)) for a in points_in]
    print(f'{len(points)} points: {time.time()-t0:.1f}s')

    from collections import Counter
    counts = Counter(fv for _, fv in points)
    majority_fv = counts.most_common(1)[0][0]
    distinct = sorted(counts.items(), key=lambda kv: -kv[1])
    entries = [
        {'a': list(a), 'f_vector': list(fv),
         'case': 'generic case' if fv == majority_fv else 'special case'}
        for a, fv in points
    ]
    out = {
        '_description': (f'n=5, d=1 parameter-space exploration (Sage), from {points_filename}. '
                          'Part of the "fun, not important" a-space investigation following '
                          'n=4,d=1 (wall a2*a4=a3^2) -- see LOGBOOK.md 2026-08-01.'),
        'n': 5, 'd': D, 'n_points': len(points),
        'distinct_f_vectors': [{'f_vector': list(fv), 'count': c} for fv, c in distinct],
        'points': entries,
    }
    out_filename = points_filename.replace('points', 'results_sage')
    path_out = os.path.join(OUTDIR, out_filename)
    with open(path_out, 'w') as f:
        json.dump(out, f, separators=(',', ':'))
    print(f'wrote {path_out}: {len(distinct)} distinct f-vectors {[c for _, c in distinct]}')
    return path_out


def run_on_points_chunk(points_filename, start, end):
    """
    Computes f-vectors for points_in[start:end] only (Python slice semantics), writing a partial
    result file for parameter_space_n5d1_parallel.py's orchestrator to merge. No majority/case
    labeling here -- that needs to see the full merged set, done in merge_chunks_with_spotcheck.
    """
    start, end = int(start), int(end)
    path_in = os.path.join(OUTDIR, points_filename)
    with open(path_in) as f:
        points_in = json.load(f)['points']
    chunk = points_in[start:end]
    t0 = time.time()
    results = [{'a': list(a), 'f_vector': list(_fvector(a))} for a in chunk]
    print(f'chunk [{start}:{end}) ({len(chunk)} points): {time.time()-t0:.1f}s')

    out_filename = points_filename.replace('.json', f'_chunk{start}-{end}.json')
    path_out = os.path.join(OUTDIR, out_filename)
    with open(path_out, 'w') as f:
        json.dump({'start': start, 'end': end, 'results': results}, f, separators=(',', ':'))
    return path_out


def merge_chunks_with_spotcheck(points_filename, chunk_paths, spotcheck_filename=None,
                                 description=''):
    """
    Merges parallel run_on_points_chunk outputs (chunk_paths, must cover the full point list
    contiguously with no gaps/overlaps) into one results file matching run_on_points' format,
    computing the majority/case labeling globally across the merged set. If spotcheck_filename is
    given (a Julia results file from a subsample -- see parameter_space_n5d1_parallel.py), each
    point gets an additional "oscar_f_vector" field: the spot-checked value if this point was
    included in that subsample, else the literal string "not computed".
    """
    all_results = []
    for cp in chunk_paths:
        with open(cp) as f:
            all_results.extend(json.load(f)['results'])

    oscar_by_a = {}
    if spotcheck_filename:
        with open(os.path.join(OUTDIR, spotcheck_filename)) as f:
            spot_data = json.load(f)
        for e in spot_data['points']:
            oscar_by_a[tuple(e['a'])] = tuple(e['f_vector'])

    from collections import Counter
    counts = Counter(tuple(r['f_vector']) for r in all_results)
    majority_fv = counts.most_common(1)[0][0]
    distinct = sorted(counts.items(), key=lambda kv: -kv[1])

    n_checked = 0
    n_mismatch = 0
    entries = []
    for r in all_results:
        a, fv = tuple(r['a']), tuple(r['f_vector'])
        entry = {'a': list(a), 'f_vector': list(fv),
                  'case': 'generic case' if fv == majority_fv else 'special case'}
        if a in oscar_by_a:
            n_checked += 1
            oscar_fv = oscar_by_a[a]
            entry['oscar_f_vector'] = list(oscar_fv)
            if oscar_fv != fv:
                n_mismatch += 1
        else:
            entry['oscar_f_vector'] = 'not computed'
        entries.append(entry)

    out = {
        '_description': description or (
            f'n=5, d=1 parameter-space exploration (Sage, parallel chunks), from '
            f'{points_filename}. oscar_f_vector: spot-check subsample cross-validated via '
            'Julia/Oscar, "not computed" elsewhere.'),
        'n': 5, 'd': D, 'n_points': len(entries),
        'n_oscar_checked': n_checked, 'n_oscar_mismatch': n_mismatch,
        'distinct_f_vectors': [{'f_vector': list(fv), 'count': c} for fv, c in distinct],
        'points': entries,
    }
    out_filename = points_filename.replace('points', 'results_sage')
    path_out = os.path.join(OUTDIR, out_filename)
    with open(path_out, 'w') as f:
        json.dump(out, f, separators=(',', ':'))
    print(f'wrote {path_out}: {len(distinct)} distinct f-vectors {[c for _, c in distinct]}, '
          f'{n_checked} Oscar-spot-checked ({n_mismatch} mismatches)')
    return path_out
