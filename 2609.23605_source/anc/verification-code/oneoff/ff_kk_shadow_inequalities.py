#!/usr/bin/env python3
"""ff_kk_shadow_inequalities.py

Changelog (reverse chronological):
  2026-09-16  cascade() now finds the leading binomial by exponential +
              binary search instead of unit steps -- the linear search made
              shadow_fn(1e8, 2) cost ~14000 comb() calls and the first run
              hit its 600 s timeout with all output still in the block
              buffer (recorded file empty).  Also: flush every section.
  2026-09-16  Created.  Companion to ff_bijection_greedy_windows.py (open
              problem 4).  Large-range exact checks of the two properties of
              the Kruskal-Katona shadow function partial_l that the greedy
              bijection's Lemma W rests on:
              (S) subadditivity partial_l(p+q) <= partial_l(p)+partial_l(q)
                  -- PROVED in the note by the disjoint-ground construction;
                  spot-checked here anyway (sampled, large values).
              (M) level monotonicity partial_l(c) <= partial_{l+1}(c)
                  -- reduced in the note (via (S)) to
              (N) partial_l(C(x,l+1)) <= C(x,l),
                  the corner statement; both checked exhaustively here.

Run:  python3 code/oneoff/ff_kk_shadow_inequalities.py
"""

import random
from math import comb


def cascade(a, level):
    out = []
    i = level
    while a > 0 and i >= 1:
        # largest ai with comb(ai, i) <= a: exponential then binary search
        hi = i
        while comb(hi + 1, i) <= a:
            hi = 2 * hi + 1
        lo = i - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if comb(mid, i) <= a:
                lo = mid
            else:
                hi = mid - 1
        out.append((lo, i))
        a -= comb(lo, i)
        i -= 1
    if a > 0:
        raise ValueError("cascade failed")
    return out


def shadow_fn(b, level):
    if b == 0:
        return 0
    return sum(comb(bi, i - 1) for bi, i in cascade(b, level))


_mu_cache = {}


def mu(a, m):
    """Max f_{m+1} given f_m = a (uncapped KK growth), m >= 1."""
    if a == 0:
        return 0
    key = (a, m)
    v = _mu_cache.get(key)
    if v is None:
        v = sum(comb(ai, i + 1) for ai, i in cascade(a, m))
        _mu_cache[key] = v
    return v


if __name__ == "__main__":
    print("predicted sizes: pure integer arithmetic; largest loop "
          "10 levels x 200001 values for (M).  No enumeration.")
    rng = random.Random(2)

    # (S) sampled, large
    bad = 0
    for _ in range(300000):
        l = rng.randint(2, 10)
        p = rng.randint(0, 10 ** 8)
        q = rng.randint(0, 10 ** 8)
        if shadow_fn(p + q, l) > shadow_fn(p, l) + shadow_fn(q, l):
            bad += 1
            if bad < 5:
                print("(S) FAIL l=%d p=%d q=%d" % (l, p, q))
    print("(S) subadditivity, sampled 300000, l<=10, p,q<=1e8: %d failures"
          % bad)

    # (M) exhaustive c <= 200000, l = 1..9; sampled to 1e9
    bad = 0
    for c in range(0, 200001):
        prev = None
        for l in range(1, 10):
            v = shadow_fn(c, l)
            if prev is not None and v < prev:
                bad += 1
                if bad < 5:
                    print("(M) FAIL c=%d l=%d: %d < %d" % (c, l, v, prev))
            prev = v
    print("(M) level monotonicity, exhaustive c<=200000, l<=9: %d failures"
          % bad)
    bad = 0
    for _ in range(200000):
        c = rng.randint(0, 10 ** 9)
        l = rng.randint(1, 11)
        if shadow_fn(c, l) > shadow_fn(c, l + 1):
            bad += 1
            if bad < 5:
                print("(M) FAIL sampled c=%d l=%d" % (c, l))
    print("(M) level monotonicity, sampled 200000, c<=1e9, l<=11: %d failures"
          % bad)

    # (N) exhaustive, extended range
    bad = 0
    checked = 0
    for l in range(2, 31):
        for x in range(l + 1, 2001):
            checked += 1
            if shadow_fn(comb(x, l + 1), l) > comb(x, l):
                bad += 1
                if bad < 5:
                    print("(N) FAIL l=%d x=%d" % (l, x))
    print("(N) partial_l(C(x,l+1)) <= C(x,l), l=2..30, x<=2000: %d checks, "
          "%d failures" % (checked, bad), flush=True)

    # (K_s) generalized corner: partial_l(C(x,l+s)) <= C(x,l+s-1)
    bad = 0
    checked = 0
    for s in range(1, 9):
        for l in range(2, 13):
            for x in range(l + s, 301):
                checked += 1
                if shadow_fn(comb(x, l + s), l) > comb(x, l + s - 1):
                    bad += 1
                    if bad < 5:
                        print("(K_s) FAIL s=%d l=%d x=%d" % (s, l, x))
    print("(K_s) partial_l(C(x,l+s)) <= C(x,l+s-1), s<=8, l<=12, x<=300: "
          "%d checks, %d failures" % (checked, bad), flush=True)

    # (APP) application-complete level monotonicity for Lemma W, r = 2:
    # for every n <= 16, 1 <= m <= m' <= n-1, 0 <= a <= C(n, m'):
    # mu_{m'}(a) <= mu_m(a).  This is every instance of (M) the r = 2
    # combinatorial surjectivity proof uses at that n, so a pass makes the
    # proof machine-complete for n <= 16.
    bad = 0
    checked = 0
    for n in range(2, 17):
        for mp in range(1, n):
            top_a = comb(n, mp)
            for m in range(1, mp):
                for a in range(0, top_a + 1):
                    checked += 1
                    if mu(a, mp) > mu(a, m):
                        bad += 1
                        if bad < 5:
                            print("(APP) FAIL n=%d m=%d m'=%d a=%d"
                                  % (n, m, mp, a))
        print("  (APP) n=%d done" % n, flush=True)
    print("(APP) all (M)-instances needed by Lemma W r=2, n<=16: %d checks, "
          "%d failures" % (checked, bad), flush=True)
    print("DONE.")
