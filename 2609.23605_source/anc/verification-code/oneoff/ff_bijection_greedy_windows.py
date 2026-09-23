#!/usr/bin/env python3
"""ff_bijection_greedy_windows.py

Changelog (reverse chronological):
  2026-09-16  (b) cascade() by exponential + binary search (the unit-step
              search made large-argument mu/shadow calls quadratic and the
              first run hit its 600 s timeout mid-suite); optional argv
              mode: "all" (default) or "part2" = exactly the sections the
              interrupted first run did not record (test B configs from
              n=5 delta>=5 onward, test C, test D).  Run with python -u.
  2026-09-16  Created.  Open problem 4 of article 2 (bijective proof of
              thm-chaining).  Tests the WINDOW normal form and the explicit
              GREEDY inverse map:

              For x in FF(d), define (absolute degree j, caps C_k(j) =
              binom(n, j-d_k)):
                  Q_i(j)  = max(0, x(j) - sum_{k>i} C_k(j)),   Q_r = x, Q_0 = 0
                  hat s_i(j - d_i) = Q_i(j) - Q_{i-1}(j).
              This is the degreewise "fill the LAST component first" greedy --
              the f-vector shadow of Amata-Crupi's lex filling (their module
              order makes g_1's monomials largest, so the QUOTIENT keeps g_r's
              slots first).

              Sections:
              (A) RECOVERY: greedy(Phi(t)) == t for every chained tuple t --
                  the elementary half of the bijection (injectivity + explicit
                  inverse), plus the window normal form (free windows
                  [indeg_i + d_i, top_i + d_i] disjoint and increasing).
              (B) LEMMA W (straightening): for an ARBITRARY tuple t, the greedy
                  slices of Phi(t) are f-vectors, chained, and resum to
                  Phi(t).  This is the KK half -- the only non-elementary step.
              (C) DUALITY equivariance: greedy commutes with the Alexander
                  gap-reversal involution on sums (rem-gap-reversal
                  compatibility of the bijection).
              (D) KK growth machinery: cascade mu_m (max f_{m+1} given f_m)
                  and shadow function; self-tests; then the two primitive
                  inequalities the r = 2 proof needs:
                  (P1) mu_m(a+b) >= mu_m(a) + mu_m(b)      [superadditivity;
                       equivalently the colex shadow fn is subadditive]
                  (P2) mu_{m'}(a) <= mu_m(a) for m' >= m   [level monotone]
                  plus the combined form mu_m(a+b) >= mu_{m'}(a) + mu_m(b).

Run:  python3 code/oneoff/ff_bijection_greedy_windows.py
"""

import sys
import os
import random
from itertools import product as iproduct
from math import comb

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))
from linusson_ff_counting import brute_fvectors, indeg, top

INF = float("inf")


# ---------------------------------------------------------------------------
# Phi, greedy, chainedness
# ---------------------------------------------------------------------------

def phi(tup, ds, n):
    """x = sum_i shift^{d_i}(s_i), as a tuple over absolute degrees
    ds[0]..ds[-1]+n (offset ds[0])."""
    lo, hi = ds[0], ds[-1] + n
    x = [0] * (hi - lo + 1)
    for s, d in zip(tup, ds):
        for m, v in enumerate(s):
            x[d - lo + m] += v
    return tuple(x)


def greedy(x, ds, n):
    """The clamp inverse: tuple of r candidate f-vectors."""
    lo = ds[0]
    r = len(ds)

    def cap(k, j):
        m = j - ds[k]
        return comb(n, m) if 0 <= m <= n else 0

    def xval(j):
        idx = j - lo
        return x[idx] if 0 <= idx < len(x) else 0

    def Q(i, j):
        # components with index > i (0-based: k = i..r-1 excluded means k>=i)
        return max(0, xval(j) - sum(cap(k, j) for k in range(i, r)))

    out = []
    for i in range(r):
        s = tuple(Q(i + 1, m + ds[i]) - Q(i, m + ds[i]) for m in range(n + 1))
        out.append(s)
    return tuple(out)


def is_chained(tup, ds, n):
    for i in range(1, len(ds)):
        if top(tup[i - 1]) >= indeg(tup[i], n) + ds[i] - ds[i - 1]:
            return False
    return True


def windows_ok(tup, ds, n):
    """Window normal form: absolute free windows disjoint and increasing:
    top_{i-1} + d_{i-1} < indeg_i + d_i (same as chained), and full-prefix/
    positive-support of each component (structural facts used in the note)."""
    for s in tup:
        t = top(s)
        rho = indeg(s, n)
        for m in range(n + 1):
            if m < rho and s[m] != comb(n, m):
                return False
            if m <= t and s[m] <= 0:
                return False
            if m > t and s[m] != 0:
                return False
    return is_chained(tup, ds, n)


# ---------------------------------------------------------------------------
# (A) recovery on chained tuples; (B) Lemma W on arbitrary tuples
# ---------------------------------------------------------------------------

def enumerate_chained(fvs, ds, n):
    """Generate chained tuples efficiently: filter component i by
    indeg > top(prev) - delta_i."""
    by_indeg = {}
    for s in fvs:
        by_indeg.setdefault(indeg(s, n), []).append(s)
    rhos = sorted(by_indeg)

    def rec(i, prefix):
        if i == len(ds):
            yield tuple(prefix)
            return
        tprev = top(prefix[-1])
        delta = ds[i] - ds[i - 1]
        for rho in rhos:
            if rho + delta > tprev:
                for s in by_indeg[rho]:
                    prefix.append(s)
                    yield from rec(i + 1, prefix)
                    prefix.pop()

    for s in fvs:
        yield from rec(1, [s])


def test_A(configs):
    print("== (A) greedy recovery on chained tuples + window normal form")
    total = bad = 0
    for n, ds in configs:
        fvs = brute_fvectors(n)
        cnt = 0
        for t in enumerate_chained(fvs, ds, n):
            cnt += 1
            total += 1
            if not windows_ok(t, ds, n):
                bad += 1
                print("   WINDOWS FAIL n=%d d=%s t=%s" % (n, ds, t))
                continue
            x = phi(t, ds, n)
            g = greedy(x, ds, n)
            if g != t:
                bad += 1
                if bad < 8:
                    print("   RECOVERY FAIL n=%d d=%s\n     t=%s\n     g=%s"
                          % (n, ds, t, g))
        print("   n=%d d=%s: %d chained tuples, all recovered: %s"
              % (n, ds, cnt, "yes" if bad == 0 else "NO"))
    print("   TOTAL: %d tuples, %d failures" % (total, bad))
    return bad


def test_B(configs, sample_configs=(), nsamples=100000, seed=20260916):
    print("== (B) Lemma W: greedy slices of Phi(arbitrary tuple)")
    rng = random.Random(seed)
    total = bad = 0
    for n, ds, mode in configs:
        fvs = brute_fvectors(n)
        fset = set(fvs)
        r = len(ds)
        if mode == "exhaustive":
            it = iproduct(fvs, repeat=r)
        else:
            it = (tuple(rng.choice(fvs) for _ in range(r))
                  for _ in range(nsamples))
        cnt = 0
        for t in it:
            cnt += 1
            total += 1
            x = phi(t, ds, n)
            g = greedy(x, ds, n)
            ok = (all(s in fset for s in g) and is_chained(g, ds, n)
                  and phi(g, ds, n) == x)
            if not ok:
                bad += 1
                if bad < 8:
                    print("   LEMMA W FAIL n=%d d=%s\n     t=%s\n     g=%s"
                          % (n, ds, t, g))
        print("   n=%d d=%s (%s): %d tuples checked" % (n, ds, mode, cnt))
    print("   TOTAL: %d tuples, %d failures" % (total, bad))
    return bad


# ---------------------------------------------------------------------------
# (C) duality equivariance
# ---------------------------------------------------------------------------

def dual_instance(x, ds, n):
    """The Alexander gap-reversal on sum-space:
    x^vee(j) = sum_k C(n, j - d'_k) - x(d_1 + d_r + n - j), on the reflected
    degree vector d'_i = d_1 + d_r - d_{r+1-i} (same gaps, reversed)."""
    dsp = [ds[0] + ds[-1] - d for d in reversed(ds)]
    lo, hi = dsp[0], dsp[-1] + n

    def xval(j):
        idx = j - ds[0]
        return x[idx] if 0 <= idx < len(x) else 0

    xv = []
    for j in range(lo, hi + 1):
        capsum = sum(comb(n, j - d) for d in dsp if 0 <= j - d <= n)
        xv.append(capsum - xval(ds[0] + ds[-1] + n - j))
    return tuple(xv), dsp


def Dvec(s, n):
    return tuple(comb(n, j) - s[n - j] for j in range(n + 1))


def test_C(configs):
    print("== (C) duality equivariance of greedy")
    total = bad = 0
    for n, ds in configs:
        fvs = brute_fvectors(n)
        seen = set()
        for t in enumerate_chained(fvs, ds, n):
            x = phi(t, ds, n)
            if x in seen:
                continue
            seen.add(x)
            total += 1
            xv, dsp = dual_instance(x, ds, n)
            g = greedy(x, ds, n)
            gv = greedy(xv, dsp, n)
            expect = tuple(Dvec(s, n) for s in reversed(g))
            if gv != expect:
                bad += 1
                if bad < 6:
                    print("   DUALITY FAIL n=%d d=%s x=%s" % (n, ds, x))
        print("   n=%d d=%s: %d sums checked" % (n, ds, len(seen)))
    print("   TOTAL: %d sums, %d failures" % (total, bad))
    return bad


# ---------------------------------------------------------------------------
# (D) KK growth machinery
# ---------------------------------------------------------------------------

def cascade(a, level):
    """Canonical cascade a = sum C(a_i, i), i = level down; a_i > a_{i-1},
    greedy.  Returns list of (a_i, i).  Leading term by binary search."""
    out = []
    i = level
    while a > 0 and i >= 1:
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


def mu(a, m):
    """Max f_{m+1} given f_m = a (no vertex cap).  m >= 1.  mu(0)=0."""
    if a == 0:
        return 0
    return sum(comb(ai, i + 1) for ai, i in cascade(a, m))


def shadow_fn(b, level):
    """Min |shadow| of b many level-sets (KK).  level >= 1."""
    if b == 0:
        return 0
    return sum(comb(bi, i - 1) for bi, i in cascade(b, level))


def mu_capped(a, m, n):
    if m == 0:
        return n if a >= 1 else 0
    return min(comb(n, m + 1), mu(a, m))


def test_D():
    print("== (D) KK machinery + primitive inequalities")
    # (D0) self-test: mu == max{b : shadow(b) <= a}, small
    bad = 0
    for m in range(1, 5):
        for a in range(0, 200):
            b = 0
            while shadow_fn(b + 1, m + 1) <= a:
                b += 1
            if mu(a, m) != b:
                bad += 1
                print("   MU/SHADOW GALOIS FAIL m=%d a=%d: mu=%d search=%d"
                      % (m, a, mu(a, m), b))
    print("   (D0) mu = Galois adjoint of shadow, m<=4, a<200: %d failures"
          % bad)
    # (D1) F_n characterization: y in F_n iff local KK conditions
    bad = 0
    for n in range(1, 7):
        fset = set(brute_fvectors(n))
        cand = 0
        agree = True
        for y in iproduct(*[range(comb(n, m) + 1) for m in range(n + 1)]):
            local = all(y[m + 1] <= mu_capped(y[m], m, n) for m in range(n))
            if local != (y in fset):
                agree = False
                bad += 1
                if bad < 5:
                    print("   CHARACTERIZATION FAIL n=%d y=%s local=%s"
                          % (n, y, local))
            cand += 1
        print("   (D1) n=%d: local-KK == membership over all %d candidate "
              "vectors: %s" % (n, cand, agree))
    # (D2) P1 same-level superadditivity, exhaustive small
    bad = 0
    checked = 0
    for m in range(1, 5):
        for a in range(0, 1200):
            ma = mu(a, m)
            for b in range(0, a + 1):        # symmetric
                checked += 1
                if mu(a + b, m) < ma + mu(b, m):
                    bad += 1
                    if bad < 6:
                        print("   P1 FAIL m=%d a=%d b=%d" % (m, a, b))
    print("   (D2) P1 mu superadditivity, m<=4, a,b<1200 exhaustive:"
          " %d checks, %d failures" % (checked, bad))
    # (D2') P1 sampled large
    rng = random.Random(1)
    bad2 = 0
    for _ in range(200000):
        m = rng.randint(1, 8)
        a = rng.randint(0, 10 ** 6)
        b = rng.randint(0, 10 ** 6)
        if mu(a + b, m) < mu(a, m) + mu(b, m):
            bad2 += 1
    print("   (D2') P1 sampled m<=8, a,b<1e6: 200000 samples, %d failures"
          % bad2)
    # (D3) P2 level monotonicity of mu, and shadow level monotonicity
    bad = 0
    for a in range(0, 5000):
        prev = None
        for m in range(1, 9):
            v = mu(a, m)
            if prev is not None and v > prev:
                bad += 1
                if bad < 6:
                    print("   P2 FAIL a=%d m=%d: mu_%d=%d > mu_%d=%d"
                          % (a, m, m, v, m - 1, prev))
            prev = v
    bads = 0
    for b in range(0, 5000):
        prev = None
        for l in range(1, 9):
            v = shadow_fn(b, l)
            if prev is not None and v < prev:
                bads += 1
                if bads < 6:
                    print("   SHADOW LEVEL-MONOT FAIL b=%d level=%d" % (b, l))
            prev = v
    print("   (D3) P2 mu level-monotone a<5000, m<=8: %d failures;"
          " shadow level-monotone: %d failures" % (bad, bads))
    # (D4) combined form mu_m(a+b) >= mu_{m'}(a) + mu_m(b), m' >= m, sampled
    bad = 0
    for _ in range(200000):
        m = rng.randint(1, 6)
        mp = rng.randint(m, 8)
        a = rng.randint(0, 10 ** 5)
        b = rng.randint(0, 10 ** 5)
        if mu(a + b, m) < mu(a, mp) + mu(b, m):
            bad += 1
    print("   (D4) combined inequality sampled, 200000 samples: %d failures"
          % bad)
    # (D5) shadow subadditivity (the P1-equivalent), exhaustive small
    bad = 0
    for l in range(2, 6):
        for p in range(0, 1200):
            sp = shadow_fn(p, l)
            for q in range(0, p + 1):
                if shadow_fn(p + q, l) > sp + shadow_fn(q, l):
                    bad += 1
                    if bad < 6:
                        print("   SHADOW SUBADD FAIL l=%d p=%d q=%d"
                              % (l, p, q))
    print("   (D5) shadow subadditivity, levels 2..5, p,q<1200 exhaustive:"
          " %d failures" % bad)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    print("mode:", mode)
    print("predicted sizes: |F_n| = 5, 10, 26, 96, 553 for n = 2..6;")
    print("largest exhaustive loops: n=4 r=3 -> 26^3 = 17576 tuples/config;")
    print("n=5 r=2 -> 9216/config; n=6 r=2 -> 305809/config (delta = 0,1,3);")
    print("n=5 r=3 sampled 100000/config.  brute_fvectors(6) enumerates")
    print("D(6) = 7828354 monotone families once (cached), ~1 min.")

    configs_B2 = ([(5, [0, 5], "exhaustive"), (5, [0, 6], "exhaustive")] +
                  [(5, [0, 0, 1], "sample"), (5, [0, 1, 2], "sample"),
                   (5, [0, 2, 2], "sample")] +
                  [(6, [0, 0], "exhaustive"), (6, [0, 1], "exhaustive"),
                   (6, [0, 3], "exhaustive")])
    if mode == "part2":
        bad = test_B(configs_B2)
        configs_C = ([(3, [0, 1]), (3, [0, 0, 1]), (3, [0, 1, 3]),
                      (4, [0, 1]), (4, [0, 2, 3]), (2, [0, 1, 1, 2])])
        bad += test_C(configs_C)
        test_D()
        print("TOTAL failures in B2/C: %d" % bad)
        print("DONE.")
        sys.exit(0)

    configs_A = ([(2, [0, d]) for d in range(0, 5)] +
                 [(3, [0, d]) for d in range(0, 6)] +
                 [(2, [0, a, a + b]) for a in range(0, 4) for b in range(0, 4)] +
                 [(3, [0, a, a + b]) for a in range(0, 5) for b in range(0, 5)] +
                 [(2, [0, 0, 1, 1]), (2, [0, 1, 1, 2]), (2, [0, 0, 0, 0])] +
                 [(4, [0, d]) for d in range(0, 6)] +
                 [(4, [0, 0, 2]), (4, [0, 1, 3]), (4, [0, 2, 3])] +
                 [(5, [0, d]) for d in range(0, 7)] +
                 [(5, [0, 0, 1]), (5, [0, 1, 3])])
    bad = test_A(configs_A)

    configs_B = ([(2, [0, d], "exhaustive") for d in range(0, 5)] +
                 [(3, [0, d], "exhaustive") for d in range(0, 6)] +
                 [(2, [0, a, a + b], "exhaustive")
                  for a in range(0, 4) for b in range(0, 4)] +
                 [(3, [0, a, a + b], "exhaustive")
                  for a in range(0, 5) for b in range(0, 5)] +
                 [(2, [0, 0, 1, 1], "exhaustive"),
                  (2, [0, 1, 2, 2], "exhaustive")] +
                 [(4, [0, d], "exhaustive") for d in range(0, 6)] +
                 [(4, [0, 0, 2], "exhaustive"), (4, [0, 1, 3], "exhaustive"),
                  (4, [0, 2, 4], "exhaustive")] +
                 [(5, [0, d], "exhaustive") for d in range(0, 7)] +
                 [(5, [0, 0, 1], "sample"), (5, [0, 1, 2], "sample"),
                  (5, [0, 2, 2], "sample")] +
                 [(6, [0, 0], "exhaustive"), (6, [0, 1], "exhaustive"),
                  (6, [0, 3], "exhaustive")])
    bad += test_B(configs_B)

    configs_C = ([(3, [0, 1]), (3, [0, 0, 1]), (3, [0, 1, 3]),
                  (4, [0, 1]), (4, [0, 2, 3]), (2, [0, 1, 1, 2])])
    bad += test_C(configs_C)

    test_D()
    print("TOTAL failures in A/B/C: %d" % bad)
    print("DONE.")
