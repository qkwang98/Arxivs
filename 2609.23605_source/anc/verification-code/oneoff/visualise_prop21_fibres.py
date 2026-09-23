#!/usr/bin/env python3
"""visualise_prop21_fibres.py -- exploring how to draw Proposition 21's fibration.

Changelog (newest first):

2026-09-14  Created.  Proposition 21 (`prop-permissive-fibres`) says the permissive f-vector set
            S_n^+ is partitioned by f_1 into padded copies of S_k, k = 0..n.  Question from Jan: is
            there a projection to a 2-dimensional affine subspace under which the slices stay
            discernible?  This script answers it with data rather than taste: it enumerates S_n^+
            exactly, measures the intrinsic dimension of each slice, and then SEARCHES small-integer
            2-d projections for ones that are injective on every slice at once.

The structural fact that makes the question easy, and which the search confirms:

  * every point of S_n^+ has f_0 = 1, so the whole set lies in an affine R^n;
  * on the slice f_1 = k, every f_j with j > k vanishes, so that slice lies in an affine
    subspace of dimension k - 1;
  * hence slices k <= 3 are at most 2-dimensional and can be drawn EXACTLY in the plane, with no
    projection at all.  Only k >= 4 needs a genuine projection.

So for n = 4 four of the five slices are exact, which is why n = 4 is the honest choice for a
figure; n = 5 needs projections for two of its six.
"""
from itertools import combinations, chain
from fractions import Fraction
import json, sys

def downward_closed(n):
    """Every order ideal of the subset lattice of [n], by backtracking.

    The first version of this brute-forced all 2^(2^n) families and checked each for downward
    closure.  That is 2^16 at n = 4 (fine) and 2^32 at n = 5 (hopeless) -- and the number of order
    ideals is only the Dedekind number, D(4) = 168 and D(5) = 7581, so the brute force was wasting
    essentially all of its work.  Here subsets are visited in nondecreasing size order and a subset
    may be admitted only once all of its facets already are, which enumerates each order ideal
    exactly once.
    """
    subs = [frozenset(s) for k in range(n + 1) for s in combinations(range(1, n + 1), k)]
    facets = [[frozenset(t) for t in combinations(sorted(s), len(s) - 1)] if s else []
              for s in subs]
    out, cur = [], set()
    def rec(i):
        if i == len(subs):
            out.append(set(cur)); return
        rec(i + 1)                                        # exclude subs[i]
        if all(f in cur for f in facets[i]):              # include, if legal
            cur.add(subs[i]); rec(i + 1); cur.remove(subs[i])
    rec(0)
    return out

def fvec(fam, n):
    return tuple(sum(1 for s in fam if len(s) == j) for j in range(n + 1))

def affine_dim(points):
    """Dimension of the affine hull of a set of integer tuples, over Q."""
    pts = [list(map(Fraction, p)) for p in points]
    if not pts: return -1
    base, rows = pts[0], [[a - b for a, b in zip(p, pts[0])] for p in pts[1:]]
    rank, ncols = 0, len(base)
    for col in range(ncols):
        piv = next((r for r in range(rank, len(rows)) if rows[r][col] != 0), None)
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pr = rows[rank]
        for r in range(len(rows)):
            if r != rank and rows[r][col] != 0:
                f = rows[r][col] / pr[col]
                rows[r] = [a - f * b for a, b in zip(rows[r], pr)]
        rank += 1
    return rank

def report(n):
    fams = [f for f in downward_closed(n) if f]          # convention (ii): non-empty
    S_plus = sorted({fvec(f, n) for f in fams})
    print("n = %d: %d non-empty order ideals, %d distinct f-vectors in S_n^+"
          % (n, len(fams), len(S_plus)))
    print("  affine dim of S_n^+ = %d (ambient R^%d, all have f_0 = 1)"
          % (affine_dim(S_plus), n + 1))
    slices = {}
    for k in range(n + 1):
        sl = sorted(p for p in S_plus if p[1] == k)
        slices[k] = sl
        print("   slice f_1 = %d: %3d points, affine dim %d%s"
              % (k, len(sl), affine_dim(sl),
                 "   <- exact in the plane" if affine_dim(sl) <= 2 else ""))
    assert sum(len(s) for s in slices.values()) == len(S_plus)
    return S_plus, slices

def search_projections(slices, n, bound=3):
    """Small-integer 2-d projections (f_2..f_n) -> R^2 injective on EVERY slice.

    Row 1 is fixed to the honest coordinate f_2 (the first non-constant entry); row 2 ranges over
    small integer combinations.  Reported in order of increasing coefficient size, so the first hit
    is the least distorted picture that separates every point.
    """
    m = n - 1                                            # coordinates f_2..f_n
    cands = []
    rng = range(-bound, bound + 1)
    def rows2():
        # prefer f_3 alone, then f_3 + small * higher coords, then anything small
        for c in sorted(( [a for a in tup] for tup in __import__('itertools').product(rng, repeat=m) ),
                        key=lambda v: (sum(abs(x) for x in v), [abs(x) for x in v])):
            if any(c): yield c
    e2 = [1] + [0] * (m - 1)
    for r2 in rows2():
        ok = True
        for k, sl in slices.items():
            seen = set()
            for p in sl:
                tail = p[2:]
                key = (sum(a * b for a, b in zip(e2, tail)),
                       sum(a * b for a, b in zip(r2, tail)))
                if key in seen: ok = False; break
                seen.add(key)
            if not ok: break
        if ok:
            cands.append(r2)
            if len(cands) >= 4: break
    return e2, cands

if __name__ == "__main__":
    out = {}
    for n in (4, 5):
        print("=" * 72)
        S_plus, slices = report(n)
        e2, cands = search_projections(slices, n)
        print("  injective-on-every-slice 2-d projections (row1 = f_2), best first:")
        for c in cands:
            print("     row2 =", c, "  i.e.  " +
                  " + ".join("%s*f_%d" % (c[i], i + 2) for i in range(len(c)) if c[i]))
        out[n] = {"S_plus": [list(p) for p in S_plus],
                  "slices": {k: [list(p) for p in v] for k, v in slices.items()},
                  "proj_row1": e2, "proj_row2": cands[0] if cands else None}
    with open("../../artefacts/prop21-fibres-data.json", "w") as f:
        json.dump(out, f, indent=1)
    print("\nwrote ../../artefacts/prop21-fibres-data.json")
