#!/usr/bin/env python3
"""linusson_ff_counting.py

Changelog (reverse chronological):
  2026-09-05  WP4+WP5: the assembled transfer-matrix count.  ff_count(n, ds)
              computes |FF(d)| (proper=False: components range over F_n;
              proper=True: over S_n, i.e. indeg >= 2 columns only) as
              u . T(delta_2) ... T(delta_r) . 1 with A from WP2's identity.
              Validated against direct sumset enumeration (independent path),
              against the recorded Macaulay2 lex-submodule counts 43/69/99/236
              (n = 3), and against the recorded proper counts of
              working-notes/discrete-vs-continuous-kup.md.
  2026-09-05  WP2: the joint (top, indeg) distribution A over F_n.
              A[tau][rho] = #{s in F_n : top(s) = tau, indeg(s) = rho} equals
              E^n(tau, rho-1) - E^n(tau-1, rho-1), with E^n(-2, .) := 0.
              A_from_linusson() computes it that way; A_bruteforce() from
              direct family enumeration; validate_A() compares them.
  2026-09-05  Created (WP1 of PLAN-linusson-ff-vector-counting.md).  Implements
              Linusson's (1999) recursion for the number of f-vectors of
              simplicial complexes -- F^p(n) and its refinement E^p(n,k),
              Theorem 5.2, transcribed from the PDF PAGE IMAGES (pages 17-19),
              not from pdftotext, which mangles the case splits of (11)/(12).
              Validated against every entry of his printed Table 5 (p = 0..9,
              n = -1..8) and Table 6 (p = 0..8, k = -1..8 plus the F^p(p)
              column), and against brute-force enumeration of downward-closed
              families (independent code path) for p <= 5.

              Verbatim statement implemented (Linusson, Theorem 5.2, for
              0 <= k, 1 <= n <= p):

                (11) F^p(n) = 1 + sum_{i=0}^n E^{p-1}(n,i) F^{p-1}(i-1)   if n < p
                     F^p(p) = 1 + F^p(p-1)                                if n = p

                (12) E^p(n,k) = sum_{i=k}^n E^{p-1}(n,i) E^{p-1}(i-1,k-1) if k <= n < p
                     E^p(p,k) = E^p(p-1,k)                                if k < n = p
                     E^p(p,p) = 1                                         if k = n = p

              with the boundary values stated in his Section 5:
              F^p(-1) = 1, F^p(0) = 2, F^0(n) = 2 (n >= 0), and for all
              p >= 0, n >= -1: E^p(n,-1) = 1, E^p(n,n) = 1, E^p(n,k) = 0
              for k > n.

              Definitions (his, cardinality-indexed: f_i = #faces of
              cardinality i, f_0 = 1 for every non-empty complex):
                F^p(n)   = #f-vectors of simplicial complexes with f_1 <= p
                           and f_j = 0 for j > n.  Both degenerate f-vectors
                           (0,0,...) [empty complex] and (1,0,...) [{emptyset}]
                           are included.
                E^p(n,k) = #f-vectors as above with f_i = binom(p,i) for
                           i <= k but f_{k+1} < binom(p,k+1).

Run:  python3 code/linusson_ff_counting.py   (runs the full validation suite)
"""

from functools import lru_cache
from itertools import combinations
from math import comb

# ----------------------------------------------------------------------------
# The recursion (Linusson, Theorem 5.2)
# ----------------------------------------------------------------------------


@lru_cache(maxsize=None)
def E(p, n, k):
    """Linusson's E^p(n,k).  Valid for p >= 0, n >= -1, any integer k >= -1."""
    if p < 0 or n < -1 or k < -1:
        raise ValueError("out of domain: E^%d(%d,%d)" % (p, n, k))
    if k == -1:
        return 1
    if k > n:
        return 0
    if k == n:
        return 1
    # now 0 <= k < n, so n >= 1
    if n > p:
        # f_1 <= p forces f_j = 0 for j > p anyway, so the constraint
        # "f_j = 0 for j > n" is vacuous once n >= p: same count as n = p.
        # (Linusson states Theorem 5.2 only for n <= p; this clause is used
        # only defensively and is exercised by the brute-force check.)
        return E(p, p, k)
    if n == p:
        return E(p, p - 1, k)                       # (12), case k < n = p
    return sum(E(p - 1, n, i) * E(p - 1, i - 1, k - 1)
               for i in range(k, n + 1))            # (12), case k <= n < p


@lru_cache(maxsize=None)
def F(p, n):
    """Linusson's F^p(n).  Valid for p >= 0, n >= -1."""
    if p < 0 or n < -1:
        raise ValueError("out of domain: F^%d(%d)" % (p, n))
    if n == -1:
        return 1
    if n == 0:
        return 2
    if p == 0:
        return 2
    if n > p:
        return F(p, p)                              # vacuous constraint, as in E
    if n == p:
        return 1 + F(p, p - 1)                      # (11), case n = p
    return 1 + sum(E(p - 1, n, i) * F(p - 1, i - 1)
                   for i in range(0, n + 1))        # (11), case n < p


# ----------------------------------------------------------------------------
# Printed tables, transcribed from the PDF page images (pages 24-25).
# Table 5: rows p = 0..9, columns n = -1..8.
# ----------------------------------------------------------------------------

TABLE_5 = {
    0: [1, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    1: [1, 2, 3, 3, 3, 3, 3, 3, 3, 3],
    2: [1, 2, 4, 5, 5, 5, 5, 5, 5, 5],
    3: [1, 2, 5, 9, 10, 10, 10, 10, 10, 10],
    4: [1, 2, 6, 16, 25, 26, 26, 26, 26, 26],
    5: [1, 2, 7, 27, 70, 95, 96, 96, 96, 96],
    6: [1, 2, 8, 43, 190, 457, 552, 553, 553, 553],
    7: [1, 2, 9, 65, 471, 2246, 4908, 5460, 5461, 5461],
    8: [1, 2, 10, 94, 1060, 9705, 48230, 95248, 100708, 100709],
    9: [1, 2, 11, 131, 2189, 35926, 398663, 2016372, 3617645, 3718353],
}

# Table 6: rows p = 0..8, columns k = -1..8, final entry F^p(p).
TABLE_6 = {
    0: ([1, 1, 0, 0, 0, 0, 0, 0, 0, 0], 2),
    1: ([1, 1, 1, 0, 0, 0, 0, 0, 0, 0], 3),
    2: ([1, 2, 1, 1, 0, 0, 0, 0, 0, 0], 5),
    3: ([1, 4, 3, 1, 1, 0, 0, 0, 0, 0], 10),
    4: ([1, 9, 10, 4, 1, 1, 0, 0, 0, 0], 26),
    5: ([1, 25, 43, 20, 5, 1, 1, 0, 0, 0], 96),
    6: ([1, 95, 267, 147, 35, 6, 1, 1, 0, 0], 553),
    7: ([1, 552, 2662, 1775, 406, 56, 7, 1, 1, 0], 5461),
    8: ([1, 5460, 47018, 38525, 8645, 966, 84, 8, 1, 1], 100709),
}


def validate_tables(verbose=True):
    """Check every printed entry of Tables 5 and 6.  Returns #mismatches."""
    bad = 0
    for p, row in TABLE_5.items():
        for j, val in enumerate(row):
            n = j - 1
            got = F(p, n)
            if got != val:
                bad += 1
                print("TABLE 5 MISMATCH: F^%d(%d) = %d, printed %d"
                      % (p, n, got, val))
    for p, (row, fval) in TABLE_6.items():
        for j, val in enumerate(row):
            k = j - 1
            got = E(p, p, k)
            if got != val:
                bad += 1
                print("TABLE 6 MISMATCH: E^%d(%d,%d) = %d, printed %d"
                      % (p, p, k, got, val))
        if F(p, p) != fval:
            bad += 1
            print("TABLE 6 MISMATCH: F^%d(%d) = %d, printed %d"
                  % (p, p, F(p, p), fval))
    if verbose:
        n5 = sum(len(r) for r in TABLE_5.values())
        n6 = sum(len(r) + 1 for r, _ in TABLE_6.values())
        print("Tables validated: %d entries (Table 5) + %d entries (Table 6),"
              " %d mismatches" % (n5, n6, bad))
    return bad


# ----------------------------------------------------------------------------
# Brute force, independent code path: enumerate downward-closed families on
# [p] directly (same method as code/oneoff/ff_vector_collision_vs_disjointness
# .py / ff_transfer_matrix_scouting.py, no Kruskal-Katona, no recursion).
# ----------------------------------------------------------------------------


@lru_cache(maxsize=None)
def brute_fvectors(p):
    """All f-vectors (f_0,...,f_p) of downward-closed families on [p],
    including the void family (all zeros) and {emptyset} = (1,0,...,0).
    Cached: the p = 6 enumeration visits ~7.8e6 monotone families."""
    subs = [frozenset(c) for k in range(1, p + 1)
            for c in combinations(range(p), k)]
    out = set()

    def rec(i, chosen):
        if i == len(subs):
            f = [0] * (p + 1)
            f[0] = 1
            for s in chosen:
                f[len(s)] += 1
            out.add(tuple(f))
            return
        rec(i + 1, chosen)
        s = subs[i]
        if all(frozenset(t) in chosen
               for t in combinations(s, len(s) - 1) if t):
            rec(i + 1, chosen | {s})

    rec(0, frozenset())
    out.add(tuple([0] * (p + 1)))
    return sorted(out)


def brute_E_F(p):
    """Brute-force values of F^p(n) for n = -1..p and E^p(n,k) for
    n = -1..p, k = -1..n, straight from the definitions."""
    fvs = brute_fvectors(p)
    Fbf = {}
    Ebf = {}
    for n in range(-1, p + 1):
        sel = [f for f in fvs if all(f[j] == 0 for j in range(n + 1, p + 1))]
        Fbf[n] = len(sel)
        for k in range(-1, n + 1):
            cnt = 0
            for f in sel:
                full = lambda i: (f[i] if i <= p else 0) == comb(p, i)
                # For k = n the "but f_{k+1} < binom(p,k+1)" clause is dropped:
                # Linusson states E^p(n,n) = 1 as a boundary value (and his
                # Table 6 diagonal E^p(p,p) = 1 confirms it), even though at
                # k = n = p the clause read literally would be vacuously false
                # (binom(p,p+1) = 0 and f_{p+1} = 0).
                if all(full(i) for i in range(0, k + 1)) and \
                        (k == n or not full(k + 1)):
                    cnt += 1
            Ebf[(n, k)] = cnt
    return Fbf, Ebf


def validate_bruteforce(pmax=5, verbose=True):
    """Compare recursion against brute force for all p <= pmax.  Returns
    #mismatches."""
    bad = 0
    for p in range(0, pmax + 1):
        Fbf, Ebf = brute_E_F(p)
        for n, val in Fbf.items():
            if F(p, n) != val:
                bad += 1
                print("BRUTE MISMATCH: F^%d(%d) = %d, brute %d"
                      % (p, n, F(p, n), val))
        for (n, k), val in Ebf.items():
            if E(p, n, k) != val:
                bad += 1
                print("BRUTE MISMATCH: E^%d(%d,%d) = %d, brute %d"
                      % (p, n, k, E(p, n, k), val))
    if verbose:
        print("Brute-force check p <= %d: %d mismatches" % (pmax, bad))
    return bad


# ----------------------------------------------------------------------------
# WP2: the joint (top, indeg) distribution over F_n = all f-vectors of
# downward-closed families on [n] (= brute_fvectors(n); f_1 <= n automatic).
#
#   indeg(s) = least j with s_j < binom(n,j)   (n+1 for the full simplex,
#                                               0 for the void family)
#   top(s)   = greatest j with s_j > 0         (-1 for the void family)
#
# Identity (WP2 of the plan):  for tau = -1..n, rho = 0..n+1,
#
#   A[tau][rho] = E^n(tau, rho-1) - E^n(tau-1, rho-1),   E^n(-2,.) := 0,
#
# because E^n(tau, rho-1) counts exactly {s in F_n : top(s) <= tau,
# indeg(s) = rho}: Linusson's "f_j = 0 for j > tau" is top <= tau, and his
# "f_i = binom(n,i) for i <= rho-1 but f_rho < binom(n,rho)" is indeg = rho
# (his k = n boundary convention handling rho = n+1, cf. WP1 wrinkle).
# Matrices are indexed A[tau+1][rho], tau+1 = 0..n+1, rho = 0..n+1.
# ----------------------------------------------------------------------------


def indeg(f, n):
    """Least j with f_j < binom(n,j); n+1 when f is the full simplex."""
    for j in range(n + 1):
        if f[j] < comb(n, j):
            return j
    return n + 1


def top(f):
    """Greatest j with f_j > 0; -1 for the void family."""
    return max([j for j, x in enumerate(f) if x > 0], default=-1)


def A_from_linusson(n):
    """A[tau+1][rho] via the E-difference identity."""
    return [[E(n, tau, rho - 1) - (E(n, tau - 1, rho - 1) if tau - 1 >= -1 else 0)
             for rho in range(n + 2)]
            for tau in range(-1, n + 1)]


def A_bruteforce(n):
    """A[tau+1][rho] from direct enumeration of downward-closed families."""
    A = [[0] * (n + 2) for _ in range(n + 2)]
    for s in brute_fvectors(n):
        A[top(s) + 1][indeg(s, n)] += 1
    return A


def validate_A(nmax=5, verbose=True):
    """Compare the two computations of A for n <= nmax.  Returns #mismatches."""
    bad = 0
    for n in range(1, nmax + 1):
        AL, AB = A_from_linusson(n), A_bruteforce(n)
        if AL != AB:
            bad += 1
            print("A MISMATCH at n = %d:\n  linusson %s\n  brute    %s"
                  % (n, AL, AB))
    if verbose:
        print("Joint-distribution identity checked for n <= %d: %d mismatches"
              % (nmax, bad))
    return bad


# ----------------------------------------------------------------------------
# WP4 / WP5: the transfer-matrix count.
#
#   |FF(d)| = sum_{tau} ( u . T(delta_2) . T(delta_3) ... T(delta_r) )[tau]
#
# where u[tau+1] = #{s : top(s) = tau} (row sums of A), and
# T(delta)[tau+1][tau'+1] = #{s : top(s) = tau', indeg(s) + delta > tau}
#                         = sum_{rho > tau - delta} A[tau'+1][rho].
# The proper variant restricts every component to S_n (indeg >= 2), i.e.
# zeroes columns rho = 0, 1 of A.
# ----------------------------------------------------------------------------


def restrict_proper(A):
    """A with the indeg = 0 and indeg = 1 columns zeroed (components in S_n)."""
    return [[0 if rho <= 1 else v for rho, v in enumerate(row)] for row in A]


def transfer_matrix(A, delta, n):
    """T(delta)[tau+1][tau'+1], tau, tau' = -1..n."""
    R = n + 2
    return [[sum(A[t2][rho] for rho in range(R) if rho + delta > t - 1)
             for t2 in range(R)] for t in range(R)]


def ff_count(n, ds, proper=False):
    """|FF(d)| (proper=False) or |FF_proper(d)| (proper=True) by the
    Linusson-transfer-matrix formula.  ds must be sorted non-decreasingly."""
    if list(ds) != sorted(ds):
        raise ValueError("shift vector must be sorted")
    A = A_from_linusson(n)
    if proper:
        A = restrict_proper(A)
    R = n + 2
    v = [sum(row) for row in A]
    for i in range(1, len(ds)):
        T = transfer_matrix(A, ds[i] - ds[i - 1], n)
        v = [sum(v[a] * T[a][b] for a in range(R)) for b in range(R)]
    return sum(v)


def ff_count_bruteforce(n, ds, proper=False):
    """|FF(d)| by direct enumeration of the sumset -- independent code path
    (no Linusson recursion, no transfer matrix, no chaining condition)."""
    from itertools import product as iproduct
    S = brute_fvectors(n)
    if proper:
        S = [s for s in S if s[0] == 1 and s[1] == n]
    N = n + max(ds) - min(ds)
    d0 = min(ds)

    def sh(x, d):
        w = [0] * (N + 1)
        for k, y in enumerate(x):
            w[d - d0 + k] = y
        return tuple(w)

    return len({tuple(sum(c) for c in zip(*[sh(s, d) for s, d in zip(t, ds)]))
                for t in iproduct(S, repeat=len(ds))})


def validate_ff_counts(verbose=True):
    """Transfer-matrix formula vs. direct sumset enumeration, both variants,
    plus the recorded external oracle values.  Returns #mismatches."""
    bad = 0
    configs = {2: [[0, 0], [0, 1], [0, 2], [0, 3], [0, 0, 0], [0, 1, 2],
                   [0, 2, 4], [0, 0, 1], [0, 1, 3], [0, 0, 0, 0], [0, 1, 2, 3]],
               3: [[0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 0, 0],
                   [0, 1, 2], [0, 0, 1], [0, 1, 3], [0, 2, 4], [0, 0, 0, 0]],
               4: [[0, 0], [0, 1], [0, 2], [0, 3], [0, 5], [0, 0, 0],
                   [0, 1, 2], [0, 0, 1], [0, 2, 4]],
               5: [[0, 0], [0, 1], [0, 2], [0, 4], [0, 6], [0, 0, 0], [0, 1, 2]],
               6: [[0, 0], [0, 1], [0, 2]]}
    for n, dss in configs.items():
        for ds in dss:
            for proper in (False, True):
                a = ff_count(n, ds, proper)
                b = ff_count_bruteforce(n, ds, proper)
                if a != b:
                    bad += 1
                    print("FF MISMATCH n=%d d=%s proper=%s: formula %d brute %d"
                          % (n, ds, proper, a, b))
    # Macaulay2 lex-submodule counts (ExteriorModules, recorded in
    # working-notes/amata-crupi-monomial-modules.org): third oracle.
    m2 = [(3, [0, 0], False, 43), (3, [0, 1], False, 69),
          (3, [-1, 2], False, 99), (3, [0, 0, 1], False, 236)]
    # Recorded proper counts, working-notes/discrete-vs-continuous-kup.md
    # (re-derived independently in code/oneoff/ff_vector_collision_vs_
    # disjointness.py):
    rec = [(n, [0, 0], True, v) for n, v in
           zip(range(2, 7), [3, 12, 69, 627, 9904])]
    rec += [(n, [0, 1], True, v) for n, v in
            zip(range(2, 7), [4, 22, 162, 1858, 38232])]
    for n, ds, proper, want in m2 + rec:
        got = ff_count(n, ds, proper)
        if got != want:
            bad += 1
            print("ORACLE MISMATCH n=%d d=%s proper=%s: formula %d recorded %d"
                  % (n, ds, proper, got, want))
    # Product-regime consistency: all gaps >= n+1 (improper) resp. n-1
    # (proper) must give |F_n|^r resp. |S_n|^r.
    for n in range(2, 7):
        for r in (2, 3, 4):
            ds = [i * (n + 1) for i in range(r)]
            if ff_count(n, ds, False) != F(n, n) ** r:
                bad += 1
                print("PRODUCT-REGIME MISMATCH (improper) n=%d r=%d" % (n, r))
            ds = [i * (n - 1) for i in range(r)]
            Sn = F(n, n) - F(n - 1, n - 1)
            if ff_count(n, ds, True) != Sn ** r:
                bad += 1
                print("PRODUCT-REGIME MISMATCH (proper) n=%d r=%d" % (n, r))
    if verbose:
        print("Transfer-matrix |FF(d)| validation: %d mismatches" % bad)
    return bad


def write_tables(path):
    """WP4/WP5 deliverable: |FF| and |FF_proper| for n = 2..8, r = 2..5,
    constant gap vectors d = (0, delta, 2*delta, ...), delta = 0..n+1."""
    lines = ["# |FF(d)| tables via the Linusson transfer-matrix formula",
             "",
             "Generated by `code/linusson_ff_counting.py` (2026-09-05); see",
             "`working-notes/counting-ff-vectors.org`.  Shift vectors are",
             "constant-gap, d = (0, delta, ..., (r-1)*delta).  For the improper",
             "count the product regime |F_n|^r starts at delta = n+1; for the",
             "proper count |S_n|^r starts at delta = n-1.",
             ""]
    for proper in (False, True):
        lines.append("## %s count" % ("Proper (components in S_n)" if proper
                                      else "Improper (components in F_n)"))
        lines.append("")
        for n in range(2, 9):
            lines.append("### n = %d   (|%s| = %d)"
                         % (n, "S_%d" % n if proper else "F_%d" % n,
                            F(n, n) - F(n - 1, n - 1) if proper else F(n, n)))
            lines.append("")
            lines.append("| delta \\ r | 2 | 3 | 4 | 5 |")
            lines.append("|---|---|---|---|---|")
            for delta in range(0, n + 2):
                row = ["| %d" % delta]
                for r in range(2, 6):
                    ds = [i * delta for i in range(r)]
                    row.append(" | %d" % ff_count(n, ds, proper))
                lines.append("".join(row) + " |")
            lines.append("")
    with open(path, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    print("wrote", path)


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "--tables":
        write_tables(sys.argv[2] if len(sys.argv) > 2
                     else "runs/counting-ff-vectors-tables.md")
    else:
        bad = validate_tables()
        bad += validate_bruteforce(5)
        bad += validate_A(5)
        bad += validate_ff_counts()
        # |S_n| = F^n(n) - F^{n-1}(n-1): proper f-vectors (f_1 = n exactly).
        S = [F(n, n) - F(n - 1, n - 1) for n in range(1, 11)]
        print("|S_n|, n = 1..10:", S)
        print("known brute-forced |S_n| 1,2,5,16,70 match:",
              S[:5] == [1, 2, 5, 16, 70])
        print("TOTAL mismatches:", bad)
