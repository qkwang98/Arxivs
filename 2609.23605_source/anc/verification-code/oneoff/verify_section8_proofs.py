#!/usr/bin/env python3
# verify_section8_proofs.py -- adversarial check of §8.3's PROOFS, not its statements.
#
# Changelog (newest first):
#
# 2026-09-10  Created. verify_section8_restated.sage checks that §8.3's *statements* are true, by
#             computing the true extremal matrix polyhedrally. That leaves the proofs unchecked,
#             and §8.3's proofs are the thinnest-provenance part of the manuscript. This script
#             checks the proofs instead: each one exhibits (or forbids) an explicit functional, so
#             here we BUILD the functional the proof specifies and test whether it really exposes
#             the intended pair of vertices uniquely. A proof whose construction fails is a broken
#             proof even when its statement is true.
#
#             Result: prop-diagonal and prop-gapK check out everywhere tested. The old
#             prop-outside-block's single construction covered only the sub-case i < d, j <= m
#             (210/210 there; 0/924 elsewhere): it FAILS at i = d, where the private block it
#             relies on is empty and no Gamma can be large enough, and it never covered j > m,
#             where the proof said only "the mirror argument" -- which is a genuinely different
#             construction, with a large POSITIVE weight on the second private block. The statement
#             was true throughout; the proof was not. The manuscript now splits it into
#             prop-row-below and prop-col-beyond, whose constructions are checked below as printed.
#
# Run:  python3 code/oneoff/verify_section8_proofs.py

from fractions import Fraction as F
from math import comb
from itertools import product

# ---------------------------------------------------------------- geometry, 1-indexed throughout


def leg(kind, n):
    if kind == "ones":
        return {s: F(1) for s in range(1, n + 1)}
    if kind == "kozlov":
        return {s: F(comb(n, s)) for s in range(1, n + 1)}
    if kind == "tent":                       # a strictly log-concave non-binomial control
        return {s: F(min(s, n + 1 - s) * 3 + 1) for s in range(1, n + 1)}
    raise ValueError(kind)


def v_vertex(a, n, d, i):
    """i-th vertex of the UNSHIFTED summand, as a dict coordinate -> value, coords 1..N."""
    return {c: a[c] for c in range(1, i + 1)}


def u_vertex(a, n, d, j):
    """j-th vertex of the summand shifted by d."""
    return {d + s: a[s] for s in range(1, j + 1)}


def val(phi, vec):
    return sum(phi.get(c, F(0)) * x for c, x in vec.items())


def exposes(phi, a, n, d, i, j):
    """Does phi uniquely maximise at v_i on summand 1 and at u_j on summand 2?"""
    v = [val(phi, v_vertex(a, n, d, k)) for k in range(1, n + 1)]
    u = [val(phi, u_vertex(a, n, d, k)) for k in range(1, n + 1)]
    ok1 = all(v[k - 1] < v[i - 1] for k in range(1, n + 1) if k != i)
    ok2 = all(u[k - 1] < u[j - 1] for k in range(1, n + 1) if k != j)
    return ok1, ok2


# ---------------------------------------------------------------- the manuscript's constructions


def phi_diagonal(a, n, d, t):
    """prop-diagonal AS PRINTED since 2026-09-10: the single threshold functional with cut at
    p = d + t, i.e. +1 on coordinates 1..d+t and -1 beyond.  This is the same functional as the
    old three-block description (+1 on [1,d], +1 on the shared block up to s = t, -1 after,
    -1 on [n+1,N]); the manuscript now writes it as one formula because one computation then
    serves both summands."""
    N = n + d
    return {c: (F(1) if c <= d + t else F(-1)) for c in range(1, N + 1)}


def phi_gapK(a, n, d, t, j, delta):
    """prop-gapK: the explicit functional, with the private blocks at +-1 (no largeness)."""
    m, N = n - d, n + d
    K = j - t
    phi = {k: F(1) for k in range(1, d + 1)}
    for c in range(n + 1, N + 1):
        phi[c] = F(-1)
    for s in range(1, m + 1):
        if s <= t:
            e = F(1)
        elif s == t + 1:
            e = F(-1) / a[t + 1]
        elif s == t + K:
            e = (1 + delta) / a[j]
        elif s < t + K:
            e = F(0)
        else:
            e = F(-1)
        phi[d + s] = e
    return phi


def phi_outside_block_as_written(a, n, d, i, j, Gamma):
    """prop-outside-block AS PRINTED: +1 on [1,i], -Gamma on (i,d], shared shaped to peak P at j,
    -Gamma on the second private block."""
    m, N = n - d, n + d
    phi = {}
    for k in range(1, i + 1):
        phi[k] = F(1)
    for k in range(i + 1, d + 1):
        phi[k] = -Gamma
    for s in range(1, m + 1):
        phi[d + s] = F(1) if s <= j else F(-1)
    for c in range(n + 1, N + 1):
        phi[c] = -Gamma
    return phi


def phi_row_below(a, n, d, i, j, M):
    """prop-row-below AS PRINTED: +1 on [1,i], -1 on (i,d], -M at d+1, and lem-shape (peak at j)
    on d+2..d+n = d+2..N.  Uniform in j: no case split at j = m."""
    N = n + d
    phi = {}
    for k in range(1, i + 1):
        phi[k] = F(1)
    for k in range(i + 1, d + 1):
        phi[k] = F(-1)
    phi[d + 1] = -M
    for s in range(2, n + 1):
        phi[d + s] = F(1) if s <= j else F(-1)
    return phi


def phi_col_beyond(a, n, d, i, j, Gamma):
    """prop-col-beyond AS PRINTED: lem-shape on [1,n] with peak at i and prescribed psi_1 = +1,
    then +Gamma on (n, d+j] and -Gamma on (d+j, N]."""
    m, N = n - d, n + d
    phi = {}
    for k in range(1, n + 1):
        phi[k] = F(1) if k <= i else F(-1)
    for s in range(m + 1, n + 1):
        phi[d + s] = Gamma if s <= j else -Gamma
    return phi


# ---------------------------------------------------------------- the checks

fails, checks = [], 0


def record(ok, msg):
    global checks
    checks += 1
    if not ok:
        fails.append(msg)


print("=== prop-diagonal (54): the constructed functional, 1 <= t <= m ===")
for kind in ("ones", "kozlov", "tent"):
    for n in range(2, 9):
        a = leg(kind, n)
        for d in range(1, n):
            m = n - d
            for t in range(1, m + 1):
                i, j = d + t, t
                ok1, ok2 = exposes(phi_diagonal(a, n, d, t), a, n, d, i, j)
                record(ok1 and ok2, f"prop-diagonal {kind} n={n} d={d} t={t}: {ok1},{ok2}")
print(f"  {checks} checks, {len(fails)} failures so far")

print("=== prop-gapK (57): the explicit functional, K >= 2, with Lambda = 1 ===")
before = len(fails)
for kind in ("kozlov", "tent"):
    for n in range(3, 9):
        a = leg(kind, n)
        for d in range(1, n):
            m = n - d
            for t in range(1, m + 1):
                for j in range(t + 2, m + 1):
                    rho = {s: a[d + s] / a[s] for s in range(1, m + 1)}
                    if not rho[t + 1] > rho[j]:
                        continue                      # hypothesis fails; proposition says nothing
                    ub = rho[t + 1] / rho[j] - 1
                    for frac in (F(1, 2), F(1, 10), F(9, 10)):
                        delta = ub * frac
                        ok1, ok2 = exposes(phi_gapK(a, n, d, t, j, delta), a, n, d, d + t, j)
                        record(ok1 and ok2,
                               f"prop-gapK {kind} n={n} d={d} t={t} j={j} delta={delta}: {ok1},{ok2}")
print(f"  {len(fails) - before} failures")

print("=== prop-row-below and prop-col-beyond, AS PRINTED in the manuscript ===")
before = len(fails)
for kind in ("ones", "kozlov", "tent"):
    for n in range(2, 8):
        a = leg(kind, n)
        for d in range(1, n):
            m = n - d
            for j in range(1, n + 1):
                for i in range(1, d + 1):                  # prop-row-below: i <= d, every j
                    ok = any(exposes(phi_row_below(a, n, d, i, j, M), a, n, d, i, j) == (True, True)
                             for M in (F(10), F(1000), F(10) ** 6))
                    record(ok, f"prop-row-below {kind} n={n} d={d} i={i} j={j}")
            for j in range(m + 1, n + 1):                  # prop-col-beyond: j > m, every i
                for i in range(1, n + 1):
                    ok = any(exposes(phi_col_beyond(a, n, d, i, j, G), a, n, d, i, j) == (True, True)
                             for G in (F(10), F(1000), F(10) ** 6))
                    record(ok, f"prop-col-beyond {kind} n={n} d={d} i={i} j={j}")
print(f"  {len(fails) - before} failures")

print()
print(f"{checks} checks total")
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails[:12]:
        print("  " + f)
    if len(fails) > 12:
        print(f"  ... and {len(fails) - 12} more")
else:
    print("ALL CHECKS PASSED")
