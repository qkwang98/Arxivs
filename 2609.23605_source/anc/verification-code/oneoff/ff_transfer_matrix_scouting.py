#!/usr/bin/env python3
"""ff_transfer_matrix_scouting.py

Changelog (reverse chronological):
  2026-09-05  Created.  Scouting for PLAN-linusson-ff-vector-counting.md: is
              Linusson's (1999) recursion for counting f-vectors extendable to
              ff-vectors?  Establishes, computationally, the two facts the plan
              is built on.

              (1) THE CHAINING REFORMULATION.  |FF(d)| equals the number of
                  r-tuples (s_1,...,s_r) of f-vectors satisfying, for i = 2..r,

                      top(s_{i-1})  <  indeg(s_i) + d_i - d_{i-1},

                  where indeg(s) = least j with s_j < binom(n,j) and
                  top(s) = greatest j with s_j > 0.  This is Amata-Crupi's
                  Definition 2.7 chaining condition on lex submodules, read off
                  the f-vectors.  It replaces "count the image of a sumset" by
                  "count tuples with a nearest-neighbour constraint".

              (2) THE TRANSFER-MATRIX FACTORISATION.  The constraint sees s_{i-1}
                  only through top and s_i only through indeg, so the count is a
                  product of (n+2)x(n+2) matrices built from the JOINT
                  DISTRIBUTION of (top, indeg) over f-vectors -- and the indeg
                  marginal of that distribution is exactly Linusson's E^p(p,k),
                  k = indeg - 1, matching his Table 6 on the nose.

              Both checked against direct enumeration of the sumset; no
              exceptions in any configuration tried.

Run:  python3 code/oneoff/ff_transfer_matrix_scouting.py
"""

from itertools import combinations, product
from math import comb


def all_fvectors(n):
    """f-vectors (f_0,...,f_n) of every downward-closed family on [n], including
    the void family (all zeros).  Singletons are NOT required -- this is the
    unrestricted set, matching Amata-Crupi's monomial ideals of E."""
    subs = [frozenset(c) for k in range(1, n + 1) for c in combinations(range(n), k)]
    out = set()

    def rec(i, chosen):
        if i == len(subs):
            f = [0] * (n + 1)
            f[0] = 1
            for s in chosen:
                f[len(s)] += 1
            out.add(tuple(f))
            return
        rec(i + 1, chosen)
        s = subs[i]
        if all(frozenset(t) in chosen for t in combinations(s, len(s) - 1) if t):
            rec(i + 1, chosen | {s})

    rec(0, frozenset())
    out.add(tuple([0] * (n + 1)))          # the void family, I = E
    return sorted(out)


def indeg(f, n):
    """indeg of the corresponding monomial ideal: least j with f_j < binom(n,j).
    Returns n+1 when the ideal is 0 (the full simplex)."""
    for j in range(n + 1):
        if f[j] < comb(n, j):
            return j
    return n + 1


def top(f):
    """Greatest j with f_j > 0; -1 for the void family.  m^t is contained in the
    ideal exactly when t > top(f)."""
    return max([j for j, x in enumerate(f) if x > 0], default=-1)


def sumset_count(S, ds, n):
    """|FF(d)|, by direct enumeration of all shifted sums."""
    N = n + max(ds)

    def sh(x, d):
        w = [0] * (N + 1)
        for k, y in enumerate(x):
            w[d + k] = y
        return tuple(w)

    return len({tuple(sum(c) for c in zip(*[sh(s, d) for s, d in zip(t, ds)]))
                for t in product(S, repeat=len(ds))})


def chaining_count(S, ds, n):
    """(1): count tuples satisfying the Definition 2.7 chaining condition."""
    info = {s: (indeg(s, n), top(s)) for s in S}
    total = 0
    for t in product(S, repeat=len(ds)):
        if all(info[t[i - 1]][1] < info[t[i]][0] + ds[i] - ds[i - 1]
               for i in range(1, len(ds))):
            total += 1
    return total


def joint_table(S, n):
    """A[top+1][indeg] = number of f-vectors with those two statistics."""
    A = [[0] * (n + 2) for _ in range(n + 2)]
    for s in S:
        A[top(s) + 1][indeg(s, n)] += 1
    return A


def transfer_count(A, ds, n):
    """(2): the same count as a product of transfer matrices."""
    R = n + 2

    def T(delta):
        return [[sum(A[t2][r] for r in range(n + 2) if (t - 1) < r + delta)
                 for t2 in range(R)] for t in range(R)]

    v = [sum(row) for row in A]
    for i in range(1, len(ds)):
        M = T(ds[i] - ds[i - 1])
        v = [sum(v[a] * M[a][b] for a in range(R)) for b in range(R)]
    return sum(v)


if __name__ == "__main__":
    # Linusson, Table 6, row E^p(p,k) for k = -1, 0, 1, ...:
    LINUSSON_TABLE_6 = {2: [1, 2, 1, 1], 3: [1, 4, 3, 1, 1],
                        4: [1, 9, 10, 4, 1, 1], 5: [1, 25, 43, 20, 5, 1, 1]}
    bad = 0
    for n in (2, 3, 4, 5):
        S = all_fvectors(n)
        A = joint_table(S, n)
        marg = [sum(A[t][r] for t in range(n + 2)) for r in range(n + 2)]
        ok = marg == LINUSSON_TABLE_6.get(n)
        bad += 0 if ok else 1
        print("n = %d   |F_n| = %d" % (n, len(S)))
        print("   indeg marginal        :", marg)
        print("   Linusson E^n(n,k)     :", LINUSSON_TABLE_6.get(n), " match:", ok)
        for ds in ([0, 0], [0, 1], [0, 2], [0, 0, 1], [0, 1, 2], [0, 1, 3]):
            direct = sumset_count(S, ds, n)
            chain = chaining_count(S, ds, n)
            trans = transfer_count(A, ds, n)
            agree = direct == chain == trans
            bad += 0 if agree else 1
            print("   d = %-10s direct %8d   chaining %8d   transfer %8d   %s"
                  % (ds, direct, chain, trans, "OK" if agree else "*** MISMATCH ***"))
    print("\ndisagreements:", bad)
