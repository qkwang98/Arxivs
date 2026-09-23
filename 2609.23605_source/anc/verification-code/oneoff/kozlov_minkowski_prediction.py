# Changelog (reverse chronological):
# 2026-08-06 22:28 - Claude: created, at Jan's request, as deliverable (a) of the
#   proper-Hilbert-functions independent-check experiment (see
#   ../artefacts/proper-hilbert-functions-kozlov-minkowski.org for the full
#   statement being tested). Pure local Kruskal-Katona + Minkowski-sum
#   computation -- no Macaulay2 -- producing the "prediction" side that
#   ../runs/rank_r_minkowski_experiment_report.md's random-sampling
#   experiment (rankr_minkowski_random_sampling_m2.py) compares against.

"""
Deliverable (a) of the rank-r Minkowski-sum stress test
(../artefacts/proper-hilbert-functions-kozlov-minkowski.org, esp. sections 3-4-7-9).

Given n and degs = (d_1=0, d_2, ..., d_r), computes:

  S : the set of PROPER Hilbert sequences (1, f_1, ..., f_n) of E/I (E = exterior
      algebra on n variables), i.e. f-vectors of simplicial complexes on the FULL
      vertex set [n] (f_1 == n exactly), via the Kruskal-Katona recursion already
      implemented in binomial_basis.py (kk_shadow_bound / enumerate_f_vectors),
      with the leading "1" (degree-0 Hilbert value) prepended to match the
      degree-0-inclusive convention of the org file's section 7. This is an
      (n+1)-tuple, NOT the n-tuple f-vector convention used by
      right_angle_simplex.py's vertex vectors.

  predicted_sumset(n, degs) : S + shift^{d_2}(S) + ... + shift^{d_r}(S), the exact
      DISCRETE sumset (not yet a convex hull) in Z^{N+1}, N = n + max(degs), using
      the org file's degree-0-inclusive shift^d (prepend d zeros to the WHOLE
      (n+1)-vector -- see section 7's explicit warning that this differs from
      right_angle_simplex.py's shift, which operates on the degree-0-DROPPED
      n-vector and needs the +e_d correction found in
      ../runs/rank2_hilbert_translation_check.md; that correction is exactly what
      the degree-0-inclusive convention here is built to avoid needing).

  predicted_polytope(n, degs) : conv(predicted_sumset(n, degs)), a Sage Polyhedron
      -- by section 9's boxed claim, this SHOULD equal
      Kozlov(n) + sum_{i=2}^r shift^{d_i}(Kozlov(n)) (both embedded degree-0-
      inclusive), and is the object deliverable (b)'s random-sampling experiment
      is checking against.

No Macaulay2 needed anywhere in this file -- everything is direct combinatorial
enumeration + Sage's Polyhedron/convex-hull machinery, deliberately independent
of deliverable (b)'s Macaulay2-based construction.
"""

load('binomial_basis.py')  # noqa: brings in kk_shadow_bound, enumerate_f_vectors


def proper_f_vectors(n):
    """
    S: the set of proper Hilbert sequences (1, f_1, ..., f_n) of E/I on n
    variables -- f-vectors of simplicial complexes on the full vertex set [n]
    (section 3: proper iff f_1 == n exactly). Built from
    binomial_basis.enumerate_f_vectors(n), which enumerates ALL f-vectors with
    f_1 in 0..n (not just f_1 == n); filtered here to the proper ones, then
    given the leading "1" prepended. Returns a sorted list of (n+1)-tuples.
    """
    all_fvecs = enumerate_f_vectors(n)
    proper = [f for f in all_fvecs if f[0] == n]
    return sorted((1,) + f for f in proper)


def shift0incl(vec, d):
    """
    The degree-0-inclusive shift^d of section 7: prepend d zeros to the WHOLE
    vector (degree-0 entry included), not the degree-0-dropped shift of
    right_angle_simplex.py. vec: a tuple/list; returns a tuple of length
    len(vec) + d.
    """
    return tuple([0] * d) + tuple(vec)


def pad_trailing(vec, N):
    """Pad vec with trailing zeros up to total length N (N >= len(vec))."""
    vec = tuple(vec)
    assert N >= len(vec)
    return vec + (0,) * (N - len(vec))


def predicted_sumset(n, degs):
    """
    S + shift^{d_2}(S) + ... + shift^{d_r}(S) (section 7's exact sumset
    identity, restricted to proper summands throughout -- section 6), as a
    sorted list of distinct (N+1)-tuples, N = n + max(degs). degs[0] must be 0
    (this project's WLOG normalization for d_1).

    Each summand S (for d_1=0) or shift^{d_i}(S) (i>=2) is first embedded in
    R^{N+1} (prepending d_i zeros, then padding trailing zeros out to length
    N+1) before summing coordinatewise over all independent choices -- an
    ordinary (exponential-size) sumset enumeration, fine at the small n, r=2
    scale this experiment uses.
    """
    assert degs[0] == 0, "degs[0] == 0 is this project's WLOG normalization"
    n = int(n)
    degs = list(degs)
    N = n + max(degs)
    S = proper_f_vectors(n)
    embedded_summands = []
    for d in degs:
        embedded_summands.append([pad_trailing(shift0incl(s, d), N + 1) for s in S])
    from itertools import product
    results = set()
    for choice in product(*embedded_summands):
        h = [0] * (N + 1)
        for part in choice:
            for k, val in enumerate(part):
                h[k] += val
        results.add(tuple(h))
    return sorted(results)


def predicted_polytope(n, degs):
    """
    conv(predicted_sumset(n, degs)) as a Sage Polyhedron in R^{N+1},
    N = n + max(degs) -- the "prediction" side of the experiment: by section
    9's boxed claim this should equal Kozlov(n) + sum_{i=2}^r
    shift^{d_i}(Kozlov(n)) in the degree-0-inclusive embedding.
    """
    pts = predicted_sumset(n, degs)
    return Polyhedron(vertices=pts)


def kozlov_polytope_degree0_inclusive(n):
    """
    Kozlov(n) directly, embedded degree-0-inclusive (section 5/9): conv(S) for
    S = proper_f_vectors(n). Provided as a standalone sanity-check building
    block -- predicted_polytope(n, [0]) (single summand, r=1) should equal
    this exactly (Kozlov's own theorem, section 5, restricted to r=1).
    """
    return Polyhedron(vertices=proper_f_vectors(n))


if __name__ in ('__main__', 'sage.all'):
    # See binomial_basis.py's own changelog for why both names are accepted:
    # `sage thisfile.py` sets __name__ = 'sage.all', not '__main__'.
    for n in (3, 4, 5):
        S = proper_f_vectors(n)
        print(f"n={n}: |S| = {len(S)} proper f-vectors")
        Kn = kozlov_polytope_degree0_inclusive(n)
        print(f"  Kozlov(n) (degree-0-inclusive): dim={Kn.dim()}, "
              f"n_vertices={Kn.n_vertices()} (expect n={n})")
        for d2 in (1, 2, 3):
            degs = (0, d2)
            P = predicted_polytope(n, degs)
            ss = predicted_sumset(n, degs)
            print(f"  degs={degs}: |sumset|={len(ss)}, predicted polytope "
                  f"dim={P.dim()}, n_vertices={P.n_vertices()}")
