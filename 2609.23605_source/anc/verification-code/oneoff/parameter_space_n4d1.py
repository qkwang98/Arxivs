# Changelog (reverse chronological):
# 2026-07-31 20:49 - Claude-Code (agent-shell, no web session): created this file. Ad-hoc, "fun,
#   not important" exploration Jan proposed after the n=4,d=1 strong-converse proof (see
#   ../artefacts/extremal-matrix-general.tex Theorem thm:strong): treat a=(a1,a2,a3,a4) as real
#   variables (not fixed to ones/kozlov) and try to partition the parameter space (mod the obvious
#   positive-scaling symmetry a -> lambda*a, which doesn't change the combinatorial type) by which
#   combinatorial type of R = angle(a) + shift^1(angle(a)) results.
#
#   Random sampling over wide ranges found only ONE f-vector, every time -- initially surprising,
#   but explained by grid-scanning + targeted probes below: there appear to be exactly TWO
#   combinatorial types for n=4, d=1, separated by the single condition a2*a4 = a3^2 (a
#   codimension-1 "wall", measure zero -- invisible to random continuous sampling, but hit
#   constantly by small-integer coincidences). This is exactly the same condition found in
#   Proposition prop:divergence's proof (there specialized to a1=a2=1: "ones" sits exactly on this
#   wall, since a1=a2=a3=a4 trivially satisfies a2*a4=a3^2; "kozlov" and generic reals sit off it).
#   Tested several OTHER natural coincidence conditions (a1=a2, a1=a3, a3=a4, a1=a4, a1*a3=a2^2,
#   a1=a2=a3, a1*a4=a2*a3) and none produced a third type -- consistent with (not a proof of) there
#   being exactly two types total.

"""
Exploration of the a=(a1,a2,a3,a4) parameter space for n=4, d=1 (the smallest (n,d) pair where
combinatorial type can depend on a -- see ../artefacts/extremal-matrix-general.tex). Not part of
the main proof pipeline; a "fun, not important" side investigation per Jan's framing.

Three sampling functions, each meant to write ONE brief results file to ../runs/ per experiment
(point + f-vector + a generic/special label, not the full per-job schema used by
../code/face_lattice_pipeline.py -- this is cheap to recompute, so the log stays brief):

    sage -c "load('parameter_space_n4d1.py'); run_random_experiment(2000, 10**6, seed=3)"
    sage -c "load('parameter_space_n4d1.py'); run_grid_experiment(10)"
    sage -c "load('parameter_space_n4d1.py'); run_targeted_probes()"
"""

import json
import os
import random
import time

load('right_angle_simplex.py')  # noqa -- brings in right_angle_minkowski_sum

OUTDIR = '../runs'
D = 1  # fixed throughout this file; n=4 is implicit in every a having 4 entries


def _fvector(a):
    R = right_angle_minkowski_sum(list(a), [0, D])
    return tuple(int(x) for x in R.f_vector())


def _save_experiment(filename, description, points):
    """
    points: list of (a, f_vector) pairs. Labels each point "generic case" or "special case" by
    comparing its f_vector against the MAJORITY f_vector seen in this experiment (data-driven,
    not hardcoded against the specific f-vectors found so far -- so a genuinely new third type in
    a future, more extensive run would still be labeled sensibly relative to that run).
    """
    os.makedirs(OUTDIR, exist_ok=True)
    from collections import Counter
    counts = Counter(fv for _, fv in points)
    majority_fv = counts.most_common(1)[0][0]
    distinct = sorted(counts.items(), key=lambda kv: -kv[1])

    entries = [
        {
            'a': [int(x) if float(x) == int(x) else float(x) for x in a],
            'f_vector': list(fv),
            'case': 'generic case' if fv == majority_fv else 'special case',
        }
        for a, fv in points
    ]
    data = {
        '_description': description,
        'n': 4, 'd': D,
        'n_points': len(points),
        'distinct_f_vectors': [{'f_vector': list(fv), 'count': c} for fv, c in distinct],
        'points': entries,
    }
    path = os.path.join(OUTDIR, filename)
    with open(path, 'w') as f:
        json.dump(data, f, separators=(',', ':'))  # compact -- brief per Jan's request, cheap to
                                                     # recompute if ever needed in expanded form
    print(f'wrote {path}: {len(points)} points, {len(distinct)} distinct f-vectors '
          f'{[c for _, c in distinct]}')
    return path


def run_random_experiment(n_points, maxval, seed=None):
    """Uniform random a_i in [1, maxval], n_points samples. Saves one file to ../runs/."""
    if seed is not None:
        random.seed(int(seed))
    t0 = time.time()
    points = []
    for _ in range(n_points):
        a = tuple(random.randint(1, maxval) for _ in range(4))
        points.append((a, _fvector(a)))
    print(f'{n_points} random points (1..{maxval}): {time.time()-t0:.1f}s')
    desc = (f'n=4, d=1 parameter-space exploration: {n_points} uniform-random points, '
            f'a_i in [1,{maxval}], seed={seed}. Part of the "fun, not important" a-space '
            'investigation following Theorem thm:strong -- see LOGBOOK.md 2026-07-31.')
    return _save_experiment(f'paramspace_n4_d1_random_max{maxval}_N{n_points}.json', desc, points)


def run_grid_experiment(K):
    """Exhaustive grid a_i in {1,...,K}^4 (K^4 points). Saves one file to ../runs/."""
    t0 = time.time()
    points = []
    for a1 in range(1, K + 1):
        for a2 in range(1, K + 1):
            for a3 in range(1, K + 1):
                for a4 in range(1, K + 1):
                    a = (a1, a2, a3, a4)
                    points.append((a, _fvector(a)))
    print(f'{K}^4={K**4} grid points: {time.time()-t0:.1f}s')
    desc = (f'n=4, d=1 parameter-space exploration: exhaustive grid a_i in 1..{K} '
            f'({K}^4={K**4} points). Part of the "fun, not important" a-space investigation '
            'following Theorem thm:strong -- see LOGBOOK.md 2026-07-31.')
    return _save_experiment(f'paramspace_n4_d1_grid_K{K}.json', desc, points)


def run_targeted_probes():
    """
    Hand-picked a's testing several natural coincidence conditions beyond the known wall
    (a2*a4=a3^2), to check for additional combinatorial types: a1=a2, a1=a3, a3=a4, a1=a4,
    a1*a3=a2^2 (an analogous condition shifted by one index), a1=a2=a3, a1*a4=a2*a3. None found a
    third type as of 2026-07-31 (see changelog above). Saves one file to ../runs/.
    """
    cases = {
        'a1=a2': [(7, 7, 3, 11), (7, 7, 5, 2), (100, 100, 37, 63)],
        'a1*a3=a2^2': [(1, 2, 4, 7), (2, 4, 8, 3), (3, 6, 12, 5)],
        'a1=a3': [(7, 3, 7, 11), (5, 9, 5, 2)],
        'a3=a4': [(7, 3, 11, 11), (2, 5, 9, 9)],
        'a1=a4': [(7, 3, 11, 7), (2, 9, 5, 2)],
        'a1=a2=a3': [(3, 3, 3, 11), (5, 5, 5, 2)],
        'a2=a3=a4': [(11, 3, 3, 3), (2, 5, 5, 5)],  # implies the known wall a2*a4=a3^2
        'a1*a4=a2*a3': [(1, 2, 3, 6), (2, 3, 5, 15)],
        'known wall a2*a4=a3^2 (control)': [(1, 1, 1, 1), (1, 1, 2, 4), (1, 3, 3, 3)],
    }
    points = []
    for label, examples in cases.items():
        for a in examples:
            points.append((a, _fvector(a)))
    desc = ('n=4, d=1 parameter-space exploration: targeted probes of several natural '
            'coincidence conditions (a1=a2, a1*a3=a2^2, a1=a3, a3=a4, a1=a4, a1=a2=a3, a2=a3=a4, '
            'a1*a4=a2*a3, plus the known wall a2*a4=a3^2 as a control), checking for additional '
            'combinatorial types beyond the known wall. See the code (run_targeted_probes '
            'docstring) for which condition each point tests.')
    return _save_experiment('paramspace_n4_d1_targeted_probes.json', desc, points)
