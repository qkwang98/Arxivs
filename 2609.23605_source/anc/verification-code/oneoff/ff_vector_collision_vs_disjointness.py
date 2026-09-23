#!/usr/bin/env python3
"""ff_vector_collision_vs_disjointness.py

Changelog (reverse chronological):
  2026-09-05  Created.  Tests the claim in
              working-notes/multigraded-hilbert-functions.org: the "forget the
              multigrading" projection

                  pi : (Z^{n+1})^r -> Z^{N+1},   (s_1,...,s_r) |-> sum_i shift^{d_i}(s_i)

              is injective on S_n^r -- equivalently |FF(d)| = |S_n|^r -- if and
              only if the index ranges {d_i+2, ..., d_i+n} are pairwise disjoint,
              i.e. iff d_{i+1} - d_i >= n-1 for every i.  That is the same
              condition under which dim Koz(n;d) attains its maximum r(n-1), so
              the "Cartesian-product regime" of the vertex-structure work, the
              full-dimensionality condition, and the no-collision condition are
              all one condition.

              Also re-derives the two ff-vector counting sequences recorded in
              working-notes/discrete-vs-continuous-kup.md as OEIS candidates
              (r=2: 3,12,69,627 for d_2=0 and 4,22,162,1858 for d_2=1), as an
              independent check of those numbers.

Run:  python3 code/oneoff/ff_vector_collision_vs_disjointness.py
"""

from itertools import combinations, product


def f_vectors_on(n):
    """f-vectors (f_0,...,f_n) of all simplicial complexes on [n], cardinality
    convention, every singleton present.  Returns a sorted list; f_0 = 1 and
    f_1 = n throughout, so this is the set S_n."""
    subsets = [frozenset(c) for k in range(2, n + 1) for c in combinations(range(n), k)]
    base = {frozenset()} | {frozenset([i]) for i in range(n)}
    out = set()

    def rec(i, chosen):
        if i == len(subsets):
            f = [0] * (n + 1)
            for s in base | chosen:
                f[len(s)] += 1
            out.add(tuple(f))
            return
        rec(i + 1, chosen)                      # exclude subsets[i]
        s = subsets[i]
        if all(frozenset(t) in base or frozenset(t) in chosen
               for t in combinations(s, len(s) - 1)):
            rec(i + 1, chosen | {s})            # include it, if downward closure allows

    rec(0, frozenset())
    return sorted(out)


def shift(v, d, N):
    w = [0] * (N + 1)
    for k, x in enumerate(v):
        w[d + k] = x
    return w


def ff_set(S, ds, n):
    N = n + max(ds)
    return {tuple(sum(c) for c in zip(*[shift(s, d, N) for s, d in zip(t, ds)]))
            for t in product(S, repeat=len(ds))}


def ranges_disjoint(ds, n):
    rs = [set(range(d + 2, d + n + 1)) for d in ds]
    return all(not (rs[i] & rs[j]) for i in range(len(rs)) for j in range(i + 1, len(rs)))


if __name__ == "__main__":
    print(" n   d              |S_n|   |S_n|^r   |FF(d)|   no collision?   ranges disjoint?")
    bad = 0
    for n in range(2, 6):
        S = f_vectors_on(n)
        for ds in ([0, 0], [0, 1], [0, 2], [0, n - 2], [0, n - 1], [0, n],
                   [0, 0, 0], [0, 1, 2], [0, n - 1, 2 * (n - 1)]):
            if any(d < 0 for d in ds):
                continue
            FF, r = ff_set(S, ds, n), len(ds)
            nocoll, disj = len(FF) == len(S) ** r, ranges_disjoint(ds, n)
            if nocoll != disj:
                bad += 1
            print(" %d   %-14s %5d   %7d   %7d   %-14s   %s%s"
                  % (n, ds, len(S), len(S) ** r, len(FF), nocoll, disj,
                     "   <-- MISMATCH" if nocoll != disj else ""))
    print("\ndisagreements:", bad)

    print("\n-- the two counting sequences, r = 2 --")
    for d2 in (0, 1):
        print("  d_2 = %d:" % d2,
              [len(ff_set(f_vectors_on(n), [0, d2], n)) for n in range(2, 6)])
    print("  |S_n|, n = 1..5:", [len(f_vectors_on(n)) for n in range(1, 6)])
