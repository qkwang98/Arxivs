#!/usr/bin/env python3
"""ffp_asymptotics_in_p_check.py

Changelog (reverse chronological):
  2026-09-16  Created (attack on open problem 1 of article 2's Section 9.2,
              rem-not-attempted): transport Linusson's Theorem 5.3 (degree)
              and Proposition 5.4 (leading coefficient) through the transfer-
              matrix product of thm-poly-p, to get the degree and leading
              coefficient of |FF^(p)(n; d)| as a polynomial in p.

              Verifies, by exact rational interpolation in p:
                (0) sanity: the p-generalised matrix count against brute-force
                    truncated sumsets (n <= 3, p <= 5, r <= 3);
                (1) Linusson's Prop 5.4 formula (13) [transcribed from the PDF
                    page image, p. 19] against interpolated E^p(m,k),
                    m <= 6, 0 <= k <= m;
                (2) the entrywise claim: deg_p A^(p)[tau][rho]
                    = C(tau+1,2) - C(rho,2), lc = lc E^p(tau,rho-1),
                    for n <= 5 and all supported (tau,rho), rho >= 1;
                (3) the degree formula
                    deg_p |FF^(p)(n;d)| = r*C(n+1,2)
                                          - sum_i C(max(1, n-delta_i+1), 2);
                (4) the leading-coefficient formula: for all gaps >= 1,
                    lc = L(n,0) * prod_i L(n, max(0, n-delta_i)),
                    L = Linusson's (13); in general, sum over degree-
                    maximising paths of products of entrywise lcs (brute path
                    enumeration over {-1..n}^r using ONLY the closed-form
                    entry data, i.e. the claimed theory, never the computed
                    polynomials).

Run:  python3 code/oneoff/ffp_asymptotics_in_p_check.py
Output: runs/ffp-asymptotics-in-p-check.txt (via tee in the driver command).
"""

import sys
from fractions import Fraction
from itertools import product as iproduct
from math import comb, factorial
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from linusson_ff_counting import E, F, brute_fvectors  # noqa: E402


def C2(x):
    return comb(x, 2)


# ---------------------------------------------------------------------------
# The p-generalised transfer objects (eq. (Ap) of thm-poly-p).
# Rows tau = -1..n  -> index t = tau+1 in 0..n+1.
# Cols rho = 0..n+1 -> index r = rho  in 0..n+1.
# ---------------------------------------------------------------------------

def A_p(n, p):
    def Esafe(m, k):
        return 0 if m < -1 else E(p, m, k)
    return [[Esafe(tau, rho - 1) - Esafe(tau - 1, rho - 1)
             for rho in range(0, n + 2)]
            for tau in range(-1, n + 1)]


def u_p(n, p, A=None):
    A = A or A_p(n, p)
    return [sum(row) for row in A]


def T_p(n, p, delta, A=None):
    A = A or A_p(n, p)
    # T(delta)[tau][tau'] = sum_{rho > tau - delta} A[tau'][rho]
    out = []
    for tau in range(-1, n + 1):
        row = []
        for taup in range(-1, n + 1):
            lo = max(0, tau - delta + 1)
            row.append(sum(A[taup + 1][rho] for rho in range(lo, n + 2)))
        out.append(row)
    return out


def count_p(n, ds, p):
    """|FF^(p)(n; d)| via thm-poly-p's product, ds sorted."""
    deltas = [ds[i] - ds[i - 1] for i in range(1, len(ds))]
    A = A_p(n, p)
    v = u_p(n, p, A)
    for d in deltas:
        T = T_p(n, p, d, A)
        v = [sum(v[i] * T[i][j] for i in range(n + 2)) for j in range(n + 2)]
    return sum(v)


# ---------------------------------------------------------------------------
# Exact interpolation: values at consecutive integers p0..p0+m ->
# Newton forward differences; polynomial iff differences vanish eventually.
# Returns (degree, leading_coefficient) and checks extra points.
# ---------------------------------------------------------------------------

def interp_deg_lc(vals):
    """vals at consecutive integer arguments.  Degree d and lc = (d-th
    forward difference)/d!, provided all later differences vanish."""
    diffs = list(vals)
    table = [diffs]
    while len(diffs) > 1:
        diffs = [diffs[i + 1] - diffs[i] for i in range(len(diffs) - 1)]
        table.append(diffs)
    deg = None
    for d in range(len(table) - 1, -1, -1):
        if any(x != 0 for x in table[d]):
            deg = d
            break
    if deg is None:
        return (-1, 0)  # zero polynomial
    # constancy of the deg-th differences over the whole window is the
    # check that the data really is a polynomial of this degree:
    row = table[deg]
    assert all(x == row[0] for x in row), "not polynomial in tested window"
    return (deg, Fraction(row[0], factorial(deg)))


# ---------------------------------------------------------------------------
# Linusson's Proposition 5.4, formula (13), transcribed from the page image:
#   lc E^p(m,k) = prod_{i=k}^{m-2} C( C(m+1,2)-C(i+1,2)-1, i )
#                 / ( C(m+1,2)-C(k+1,2) )!
# empty product = 1 when k >= m-1; lc F^p(m) = L(m,0).
# ---------------------------------------------------------------------------

def L(m, k):
    num = 1
    for i in range(k, m - 1):
        num *= comb(C2(m + 1) - C2(i + 1) - 1, i)
    return Fraction(num, factorial(C2(m + 1) - C2(k + 1)))


# ---------------------------------------------------------------------------
# Closed-form entrywise data (the claims to be verified / then used):
#   deg A^(p)[tau][rho] = C2(tau+1) - C2(rho), lc = L(tau, rho-1),
#     for tau >= 0, 1 <= rho <= tau+1;  A[.][0] = e_{-1};  A[-1][.] = e_0.
# Entry data for u and T(delta) follow by summation (dominant term:
# smallest admissible rho).
# ---------------------------------------------------------------------------

NEG = None  # marker for the zero polynomial


def entry_A(tau, rho):
    """(deg, lc) of A^(p)[tau][rho], or NEG."""
    if tau == -1:
        return (0, Fraction(1)) if rho == 0 else NEG
    if rho == 0:
        return NEG
    if rho > tau + 1:
        return NEG
    return (C2(tau + 1) - C2(rho), L(tau, rho - 1))


def entry_u(tau):
    if tau == -1:
        return (0, Fraction(1))
    return (C2(tau + 1), L(tau, 0))     # dominant rho = 1 (rho=0 col is 0)


def entry_T(delta, tau, taup):
    """(deg, lc) of T^(p)(delta)[tau][taup], or NEG."""
    if taup == -1:
        return (0, Fraction(1)) if tau <= delta - 1 else NEG
    rstar = max(1, tau - delta + 1)
    if rstar > taup + 1:
        return NEG
    return (C2(taup + 1) - C2(rstar), L(taup, rstar - 1))


def predicted_paths(n, deltas):
    """(deg, lc) of the whole product, from closed-form entry data only:
    brute enumeration of all paths in {-1..n}^r, max-plus with lc-summing."""
    r = len(deltas) + 1
    best_deg, best_lc = None, Fraction(0)
    for path in iproduct(range(-1, n + 1), repeat=r):
        e = entry_u(path[0])
        if e is NEG:
            continue
        deg, lc = e
        dead = False
        for i, d in enumerate(deltas):
            e = entry_T(d, path[i], path[i + 1])
            if e is NEG:
                dead = True
                break
            deg += e[0]
            lc *= e[1]
        if dead:
            continue
        if best_deg is None or deg > best_deg:
            best_deg, best_lc = deg, lc
        elif deg == best_deg:
            best_lc += lc
    return best_deg, best_lc


def predicted_closed(n, deltas):
    """Degree formula (all gaps); lc product formula (positive gaps only)."""
    r = len(deltas) + 1
    deg = r * C2(n + 1) - sum(C2(max(1, n - d + 1)) for d in deltas)
    if all(d >= 1 for d in deltas):
        lc = L(n, 0)
        for d in deltas:
            lc *= L(n, max(0, n - d))
    else:
        lc = None
    return deg, lc


# ---------------------------------------------------------------------------
# (0) brute-force truncated sumsets at general p (independent path)
# ---------------------------------------------------------------------------

def brute_count(n, p, ds):
    fvs = [f for f in brute_fvectors(p) if all(x == 0 for x in f[n + 1:])]
    L_ = len(ds)
    hi = ds[-1] + p + 1
    sums = set()
    for tup in iproduct(fvs, repeat=L_):
        v = [0] * hi
        for f, d in zip(tup, ds):
            for j, x in enumerate(f):
                if x:
                    v[j + d] += x
        sums.add(tuple(v))
    return len(sums)


def main():
    fails = 0

    print("== (0) matrix count vs brute-force truncated sumset ==")
    for n, p, ds in [(2, 3, (0, 0)), (2, 4, (0, 1)), (2, 5, (0, 2)),
                     (3, 4, (0, 0)), (3, 5, (0, 1)), (3, 5, (0, 3)),
                     (2, 4, (0, 0, 1)), (3, 4, (0, 1, 1)),
                     (2, 5, (0, 2, 3)), (1, 5, (0, 0))]:
        mc, bc = count_p(n, ds, p), brute_count(n, p, ds)
        ok = mc == bc
        fails += not ok
        print("  n=%d p=%d d=%s : matrix %d brute %d %s"
              % (n, p, str(ds), mc, bc, "OK" if ok else "FAIL"))

    print("== (1) Linusson Prop 5.4 formula (13) vs interpolated E^p(m,k) ==")
    for m in range(0, 7):
        for k in range(0, m + 1):
            dpred = C2(m + 1) - C2(k + 1)
            vals = [E(p, m, k) for p in range(m, m + dpred + 6)]
            deg, lc = interp_deg_lc(vals)
            ok = (deg == dpred and lc == L(m, k))
            fails += not ok
            if not ok:
                print("  FAIL E^p(%d,%d): deg %s pred %d lc %s pred %s"
                      % (m, k, deg, dpred, lc, L(m, k)))
    print("  all (m,k), m<=6: degree C(m+1,2)-C(k+1,2) and lc (13) confirmed"
          if fails == 0 else "  (failures above)")

    print("== (2) entrywise deg/lc of A^(p), n<=5 ==")
    bad2 = 0
    for n in range(1, 6):
        for tau in range(-1, n + 1):
            for rho in range(0, n + 2):
                pred = entry_A(tau, rho)
                dmax = 0 if pred is NEG else pred[0]
                vals = [A_p(n, p)[tau + 1][rho]
                        for p in range(n, n + dmax + 6)]
                deg, lc = interp_deg_lc(vals)
                if pred is NEG:
                    ok = (deg == -1)
                else:
                    ok = (deg, lc) == pred
                bad2 += not ok
                if not ok:
                    print("  FAIL A^(p)[%d][%d] at n=%d: got (%s,%s), "
                          "pred %s" % (tau, rho, n, deg, lc, str(pred)))
    fails += bad2
    print("  all entries, n=1..5: confirmed" if bad2 == 0
          else "  %d mismatches" % bad2)

    print("== (3)+(4) degree and lc of |FF^(p)(n;d)| ==")
    configs = []
    for n in range(1, 6):
        for d in range(0, n + 3):
            configs.append((n, (d,)))
    for n in range(1, 5):
        for d2 in range(0, n + 2):
            for d3 in range(0, n + 2):
                configs.append((n, (d2, d3)))
    for n in (2, 3):
        for gaps in [(0, 0, 0), (1, 0, 2), (0, n, 0), (2, 1, 0),
                     (1, 1, 1), (n + 1, 0, 1), (n, n, n)]:
            configs.append((n, gaps))
    configs.append((5, (2, 4)))
    configs.append((5, (0, 3)))

    bad3 = 0
    for n, gaps in configs:
        ds = [0]
        for g in gaps:
            ds.append(ds[-1] + g)
        r = len(ds)
        dbound = r * C2(n + 1)
        vals = [count_p(n, tuple(ds), p) for p in range(n, n + dbound + 6)]
        deg, lc = interp_deg_lc(vals)
        pdeg_c, plc_c = predicted_closed(n, gaps)
        pdeg_p, plc_p = predicted_paths(n, gaps)
        ok = (deg == pdeg_c == pdeg_p and lc == plc_p
              and (plc_c is None or lc == plc_c))
        bad3 += not ok
        tag = "OK " if ok else "FAIL"
        print("  %s n=%d gaps=%-10s deg=%3d (closed %3d, paths %3d)  "
              "lc=%s%s"
              % (tag, n, str(gaps), deg, pdeg_c, pdeg_p, lc,
                 "" if plc_c is None else " = closed-form product"))
    fails += bad3

    print()
    print("TOTAL FAILURES: %d" % fails)
    return fails


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
