#!/usr/bin/env python3
"""ff_transfer_spectra.py

Changelog (reverse chronological):
  2026-09-05  Created.  WP6 of PLAN-linusson-ff-vector-counting.md: growth of
              |FF(n; constant gap delta)| in r.
              (1) Perron roots and characteristic polynomials of the transfer
                  matrices T(delta) (improper and proper variants), n = 2..6.
              (2) delta = 0: T(0) is unipotent (proved in the note); check the
                  exact polynomial degree of r |-> |FF(n; 0^r)| by finite
                  differences (expected n+1).
              (3) The two-parameter (p, n) generalization: components with
                  f_1 <= p and dimension <= n-1.  Transfer count with
                  A^(p)[tau][rho] = E^p(tau,rho-1) - E^p(tau-1,rho-1) vs.
                  brute-force sumset enumeration over truncated families on
                  [p]; and finite differences in p to exhibit polynomiality.

Run:  cd code && python3 oneoff/ff_transfer_spectra.py
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from itertools import product as iproduct
from linusson_ff_counting import (E, F, A_from_linusson, restrict_proper,
                                  transfer_matrix, ff_count, brute_fvectors)
import sympy


def perron_table():
    print("== (1) Perron roots of T(delta)  (improper | proper)")
    for n in range(2, 7):
        A = A_from_linusson(n)
        Ap = restrict_proper(A)
        for delta in range(1, n + 1):
            row = []
            for mat in (A, Ap):
                T = sympy.Matrix(transfer_matrix(mat, delta, n))
                # exact real roots of the charpoly; Perron root = largest.
                cp = T.charpoly()
                lam = max(cp.real_roots())
                row.append(sympy.Float(lam.evalf(15), 12))
            print("   n=%d delta=%d: %s | %s" % (n, delta, row[0], row[1]))
        # charpoly of T(1) improper, for the record, small n only
        if n <= 4:
            T = sympy.Matrix(transfer_matrix(A, 1, n))
            print("   n=%d charpoly T(1) improper: %s"
                  % (n, sympy.factor(T.charpoly().as_expr())))


def delta0_degrees():
    print("== (2) delta = 0: polynomial degree of r |-> |FF(n;0^r)|")
    for n in range(2, 8):
        for proper in (False, True):
            vals = [ff_count(n, [0] * r, proper) for r in range(1, n + 6)]
            d = 0
            seq = vals[:]
            while any(x != seq[0] for x in seq) and d < len(vals) - 1:
                seq = [b - a for a, b in zip(seq, seq[1:])]
                d += 1
            print("   n=%d proper=%s: degree %d (expected n+1 = %d)  values %s"
                  % (n, proper, d, n + 1, vals[:5]))


def A_pn(p, n):
    """A^(p)[tau+1][rho]: joint (top, indeg) count over f-vectors with
    f_1 <= p, dimension <= n-1 (top <= n), indeg w.r.t. binom(p,.)."""
    return [[E(p, tau, rho - 1) - (E(p, tau - 1, rho - 1) if tau >= 0 else 0)
             for rho in range(n + 2)]
            for tau in range(-1, n + 1)]


def ff_count_pn(p, n, ds):
    A = A_pn(p, n)
    R = n + 2
    v = [sum(row) for row in A]
    for i in range(1, len(ds)):
        T = transfer_matrix(A, ds[i] - ds[i - 1], n)
        v = [sum(v[a] * T[a][b] for a in range(R)) for b in range(R)]
    return sum(v)


def indeg_p(f, p):
    from math import comb
    for j in range(len(f)):
        if f[j] < comb(p, j):
            return j
    return len(f)


def ff_count_pn_bruteforce(p, n, ds):
    """Sumset over truncated families: f-vectors on [p] with top <= n."""
    S = [s for s in brute_fvectors(p) if all(x == 0 for x in s[n + 1:])]
    N = n + max(ds)

    def sh(x, d):
        w = [0] * (N + 1)
        for k, y in enumerate(x[:n + 1]):
            w[d + k] = y
        return tuple(w)

    return len({tuple(sum(c) for c in zip(*[sh(s, d) for s, d in zip(t, ds)]))
                for t in iproduct(S, repeat=len(ds))})


def pn_generalization():
    print("== (3) two-parameter (p, n): transfer vs brute force, and p-degrees")
    bad = 0
    for n in (1, 2, 3):
        for p in range(n, 6):
            for ds in ([0, 0], [0, 1], [0, 0, 0], [0, 1, 2]):
                a = ff_count_pn(p, n, ds)
                b = ff_count_pn_bruteforce(p, n, ds)
                ok = a == b
                bad += 0 if ok else 1
                if not ok:
                    print("   MISMATCH p=%d n=%d d=%s: %d vs %d"
                          % (p, n, ds, a, b))
    print("   brute-force comparisons: %d mismatches" % bad)
    for n in (2, 3):
        for ds in ([0, 0], [0, 1]):
            vals = [ff_count_pn(p, n, ds) for p in range(n, n + 25)]
            seq = vals[:]
            d = 0
            while any(x != seq[0] for x in seq) and d < 24:
                seq = [y - x for x, y in zip(seq, seq[1:])]
                d += 1
            print("   n=%d d=%s: |FF^(p)| = %s ... polynomial in p of degree %d"
                  % (n, ds, vals[:4], d))
    return bad


if __name__ == "__main__":
    perron_table()
    delta0_degrees()
    pn_generalization()
