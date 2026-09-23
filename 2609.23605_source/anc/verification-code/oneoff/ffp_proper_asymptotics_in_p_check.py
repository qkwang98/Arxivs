#!/usr/bin/env python3
"""ffp_proper_asymptotics_in_p_check.py

Changelog (reverse chronological):
  2026-09-16  Created (the proper-variant gap left open by
              working-notes/ffp-asymptotics-proof.org, "What this does not
              settle"): do the entrywise degree bookkeeping on the
              deleted-column block of the proper transfer matrices, i.e.
              transport Linusson's Theorem 5.3 / Proposition 5.4 through
              u' T'(delta_2) ... T'(delta_r) 1 with A' = A^(p) with columns
              rho = 0, 1 zeroed (thm-proper's deletion, at general p).

              Verifies, by exact rational interpolation in p:
                (0) sanity: the proper p-generalised matrix count against
                    brute-force truncated PROPER sumsets (components with
                    f_0 = 1, f_1 = p), n <= 3, p <= 5, r <= 3;
                (1) structure: rows tau = -1, 0 of A'^(p) vanish, hence
                    u'[-1] = u'[0] = 0 and columns tau' = -1, 0 of T'(delta)
                    vanish -- the count lives on the block tau in {1..n}
                    (the delta0-exact-degrees precedent, now at general p);
                (2) the entrywise claims on the block: for tau >= 1,
                      deg u'^(p)[tau] = C(tau+1,2) - 1,   lc = L(tau,1);
                    and with rstar' = max(2, tau - delta + 1),
                      T'^(p)(delta)[tau][tau'] = 0 iff rstar' > tau'+1, else
                      deg = C(tau'+1,2) - C(rstar',2), lc = L(tau', rstar'-1);
                (3) the degree formula (kappa'_i = max(1, n - delta_i)):
                    deg_p |FF^(p)_pr(n;d)| = r*C(n+1,2) - 1
                                             - sum_i C(kappa'_i + 1, 2);
                (4) the leading coefficient: for all gaps >= 1,
                    lc = L(n,1) * prod_i L(n, kappa'_i)  (unique all-n path);
                    in general the sum over degree-maximising paths in
                    {1..n}^r of products of entrywise lcs, computed from the
                    closed-form entry data ONLY, never from the polynomials;
                (5) the p-analogue of prop-proper-threshold:
                    |FF^(p)_pr| = |S_n^(p)|^r iff every gap >= n-1, with
                    |S_n^(p)| = sum_{k=1}^n E^p(n,k).

Run:  python3 code/oneoff/ffp_proper_asymptotics_in_p_check.py
Output: runs/ffp-proper-asymptotics-in-p-check.txt (via tee in the driver).
"""

import sys
from fractions import Fraction
from itertools import product as iproduct
from math import comb, factorial
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from linusson_ff_counting import E, brute_fvectors  # noqa: E402


def C2(x):
    return comb(x, 2)


# ---------------------------------------------------------------------------
# The proper p-generalised transfer objects: A'^(p) = A^(p) with columns
# rho = 0, 1 zeroed (thm-proper's deletion applied to eq. (Ap)).
# Rows tau = -1..n -> index tau+1; cols rho = 0..n+1 -> index rho.
# ---------------------------------------------------------------------------

def A_p(n, p):
    def Esafe(m, k):
        return 0 if m < -1 else E(p, m, k)
    return [[Esafe(tau, rho - 1) - Esafe(tau - 1, rho - 1)
             for rho in range(0, n + 2)]
            for tau in range(-1, n + 1)]


def A_p_proper(n, p):
    return [[0 if rho <= 1 else v for rho, v in enumerate(row)]
            for row in A_p(n, p)]


def u_p_proper(n, p, Ap=None):
    Ap = Ap or A_p_proper(n, p)
    return [sum(row) for row in Ap]


def T_p_proper(n, p, delta, Ap=None):
    Ap = Ap or A_p_proper(n, p)
    out = []
    for tau in range(-1, n + 1):
        row = []
        for taup in range(-1, n + 1):
            lo = max(0, tau - delta + 1)
            row.append(sum(Ap[taup + 1][rho] for rho in range(lo, n + 2)))
        out.append(row)
    return out


def count_p_proper(n, ds, p):
    """|FF^(p)_pr(n; d)| via the proper transfer product, ds sorted."""
    deltas = [ds[i] - ds[i - 1] for i in range(1, len(ds))]
    Ap = A_p_proper(n, p)
    v = u_p_proper(n, p, Ap)
    for d in deltas:
        T = T_p_proper(n, p, d, Ap)
        v = [sum(v[i] * T[i][j] for i in range(n + 2)) for j in range(n + 2)]
    return sum(v)


def S_p(n, p):
    """|S_n^(p)| = #{f-vectors on p vertices, top <= n, indeg >= 2}."""
    return sum(E(p, n, k) for k in range(1, n + 1))


# ---------------------------------------------------------------------------
# Exact interpolation (same as the improper battery): Newton forward
# differences with the window-constancy of the top difference asserted.
# ---------------------------------------------------------------------------

def interp_deg_lc(vals):
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
        return (-1, 0)
    row = table[deg]
    assert all(x == row[0] for x in row), "not polynomial in tested window"
    return (deg, Fraction(row[0], factorial(deg)))


# ---------------------------------------------------------------------------
# Linusson's Proposition 5.4, formula (13) (page-image transcription,
# verified against interpolated E^p(m,k) in the improper battery).
# ---------------------------------------------------------------------------

def L(m, k):
    num = 1
    for i in range(k, m - 1):
        num *= comb(C2(m + 1) - C2(i + 1) - 1, i)
    return Fraction(num, factorial(C2(m + 1) - C2(k + 1)))


# ---------------------------------------------------------------------------
# Closed-form entrywise data on the block tau in {1..n} (the claims):
#   u'[tau]: dominant rho = 2 -> deg C2(tau+1) - 1, lc L(tau,1);
#   T'(delta)[tau][tau']: rstar' = max(2, tau-delta+1), zero iff
#     rstar' > tau'+1, else deg C2(tau'+1) - C2(rstar'), lc L(tau', rstar'-1).
# ---------------------------------------------------------------------------

NEG = None


def entry_u_pr(tau):
    if tau < 1:
        return NEG
    return (C2(tau + 1) - 1, L(tau, 1))


def entry_T_pr(delta, tau, taup):
    if taup < 1:
        return NEG
    rstar = max(2, tau - delta + 1)
    if rstar > taup + 1:
        return NEG
    return (C2(taup + 1) - C2(rstar), L(taup, rstar - 1))


def predicted_paths(n, deltas):
    """(deg, lc) of the proper product from closed-form entry data only:
    brute enumeration of paths in {1..n}^r, max-plus with lc-summing."""
    r = len(deltas) + 1
    best_deg, best_lc = None, Fraction(0)
    for path in iproduct(range(1, n + 1), repeat=r):
        e = entry_u_pr(path[0])
        if e is NEG:
            continue
        deg, lc = e
        dead = False
        for i, d in enumerate(deltas):
            e = entry_T_pr(d, path[i], path[i + 1])
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
    deg = r * C2(n + 1) - 1 - sum(C2(max(1, n - d) + 1) for d in deltas)
    if all(d >= 1 for d in deltas):
        lc = L(n, 1)
        for d in deltas:
            lc *= L(n, max(1, n - d))
    else:
        lc = None
    return deg, lc


# ---------------------------------------------------------------------------
# (0) brute-force truncated PROPER sumsets at general p (independent path)
# ---------------------------------------------------------------------------

def brute_count_proper(n, p, ds):
    fvs = [f for f in brute_fvectors(p)
           if all(x == 0 for x in f[n + 1:]) and f[0] == 1 and f[1] == p]
    hi = ds[-1] + p + 1
    sums = set()
    for tup in iproduct(fvs, repeat=len(ds)):
        v = [0] * hi
        for f, d in zip(tup, ds):
            for j, x in enumerate(f):
                if x:
                    v[j + d] += x
        sums.add(tuple(v))
    return len(sums)


def main():
    fails = 0

    print("== (0) proper matrix count vs brute-force truncated proper "
          "sumset ==")
    for n, p, ds in [(2, 3, (0, 0)), (2, 4, (0, 1)), (2, 5, (0, 2)),
                     (3, 4, (0, 0)), (3, 5, (0, 1)), (3, 5, (0, 3)),
                     (2, 4, (0, 0, 1)), (3, 4, (0, 1, 1)),
                     (2, 5, (0, 2, 3)), (1, 5, (0, 0))]:
        mc, bc = count_p_proper(n, ds, p), brute_count_proper(n, p, ds)
        ok = mc == bc
        fails += not ok
        print("  n=%d p=%d d=%s : matrix %d brute %d %s"
              % (n, p, str(ds), mc, bc, "OK" if ok else "FAIL"))

    print("== (1) structure: dead rows of A'^(p), dead columns of T', "
          "u'[-1]=u'[0]=0 ==")
    bad1 = 0
    for n in range(1, 6):
        for p in range(n, n + 8):
            Ap = A_p_proper(n, p)
            if any(Ap[0]) or any(Ap[1]):
                bad1 += 1
                print("  FAIL nonzero row tau=-1/0 at n=%d p=%d" % (n, p))
            u = u_p_proper(n, p, Ap)
            if u[0] != 0 or u[1] != 0:
                bad1 += 1
                print("  FAIL u'[-1] or u'[0] nonzero at n=%d p=%d" % (n, p))
            for delta in range(0, n + 3):
                T = T_p_proper(n, p, delta, Ap)
                if any(T[t][0] for t in range(n + 2)) or \
                        any(T[t][1] for t in range(n + 2)):
                    bad1 += 1
                    print("  FAIL nonzero column tau'=-1/0, n=%d p=%d "
                          "delta=%d" % (n, p, delta))
    fails += bad1
    print("  n=1..5, p=n..n+7, delta=0..n+2: confirmed" if bad1 == 0
          else "  %d failures" % bad1)

    print("== (2) entrywise deg/lc of u'^(p) and T'^(p)(delta) on the "
          "block, n<=5 ==")
    bad2 = 0
    for n in range(1, 6):
        for tau in range(1, n + 1):
            pred = entry_u_pr(tau)
            vals = [u_p_proper(n, p)[tau + 1]
                    for p in range(n, n + pred[0] + 6)]
            got = interp_deg_lc(vals)
            if got != pred:
                bad2 += 1
                print("  FAIL u'[%d] at n=%d: got %s pred %s"
                      % (tau, n, got, pred))
        for delta in range(0, n + 3):
            for tau in range(1, n + 1):
                for taup in range(1, n + 1):
                    pred = entry_T_pr(delta, tau, taup)
                    dmax = 0 if pred is NEG else pred[0]
                    vals = [T_p_proper(n, p, delta)[tau + 1][taup + 1]
                            for p in range(n, n + dmax + 6)]
                    got = interp_deg_lc(vals)
                    ok = (got[0] == -1) if pred is NEG else (got == pred)
                    bad2 += not ok
                    if not ok:
                        print("  FAIL T'(%d)[%d][%d] at n=%d: got %s pred %s"
                              % (delta, tau, taup, n, got, str(pred)))
    fails += bad2
    print("  all block entries, n=1..5, delta=0..n+2: confirmed" if bad2 == 0
          else "  %d mismatches" % bad2)

    print("== (3)+(4) degree and lc of |FF^(p)_pr(n;d)| ==")
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
        vals = [count_p_proper(n, tuple(ds), p)
                for p in range(n, n + dbound + 6)]
        deg, lc = interp_deg_lc(vals)
        pdeg_c, plc_c = predicted_closed(n, gaps)
        pdeg_p, plc_p = predicted_paths(n, gaps)
        ok = (deg == pdeg_c == pdeg_p and lc == plc_p
              and (plc_c is None or lc == plc_c))
        bad3 += not ok
        tag = "OK " if ok else "FAIL"
        print("  %s n=%d gaps=%-10s deg=%3d (closed %3d, paths %3d)  lc=%s%s"
              % (tag, n, str(gaps), deg, pdeg_c, pdeg_p, lc,
                 "" if plc_c is None else " = closed-form product"))
    fails += bad3

    print("== (5) p-analogue of prop-proper-threshold: product regime iff "
          "all gaps >= n-1 ==")
    bad5 = 0
    for n in range(2, 5):
        for r in (2, 3):
            for delta in range(max(0, n - 3), n + 1):
                ds = tuple(i * delta for i in range(r))
                vac = delta >= n - 1
                for p in range(n, n + 6):
                    eq = count_p_proper(n, ds, p) == S_p(n, p) ** r
                    if eq != vac:
                        bad5 += 1
                        print("  FAIL n=%d r=%d delta=%d p=%d: product "
                              "regime %s, expected %s"
                              % (n, r, delta, p, eq, vac))
    fails += bad5
    print("  n=2..4, r=2..3, delta=n-3..n, p=n..n+5: confirmed" if bad5 == 0
          else "  %d failures" % bad5)

    print()
    print("TOTAL FAILURES: %d" % fails)
    return fails


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
