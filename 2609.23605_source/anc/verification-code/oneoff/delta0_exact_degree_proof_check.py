#!/usr/bin/env python3
"""delta0_exact_degree_proof_check.py

Changelog (reverse chronological):
  2026-09-15  Created.  Numerical verification of every step of the proposed
              PROOF of the exact delta=0 degrees (open problem 2 of article 2
              Section 9.2; Remark rem-delta0-degrees records them as observed
              only).  The proof reduces the degree of the polynomial
              r |-> u . T(0)^{r-1} . 1 to the largest k with u N^k 1 != 0,
              N = T(0) - I nilpotent, and then evaluates that bracket as a
              CORNER ENTRY of a strictly-upper-triangular power:

                improper:  u N^{n+1} 1 = prod_{j=0}^{n}   binom(n,j)  > 0,
                proper:    u' N'^{n-1} 1 = prod_{j=2}^{n} binom(n,j)  > 0
                           (N' = restriction of T'(0) - I to the invariant
                           block tau = 1..n; T'(0) itself is NOT unipotent
                           on the full index set - eigenvalues 0,0,1,...,1),

              resting on two structural facts about the joint distribution A:
                (S1)  A[j][j+1] = 1 for 0 <= j <= n   (full truncation at j),
                (S2)  A[j][j]   = binom(n,j) - 1 for 1 <= j <= n, and
                      A[0][0] = 0; row tau=-1 of A is e_0 (void family only).
              Every claim is checked here for n = 2..8, and the resulting
              polynomial sum_k binom(r-1,k) (u N^k 1) is cross-checked against
              the independent transfer-matrix count ff_count(n, [0]*r) of
              code/linusson_ff_counting.py for r = 1..n+4, both variants,
              with finite differences confirming the degree.

Run:  systemd-run --user --scope -p MemoryMax=8G timeout 600 \
        python3 code/oneoff/delta0_exact_degree_proof_check.py
"""

import sys
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from linusson_ff_counting import A_from_linusson, ff_count  # noqa: E402

NMIN, NMAX = 2, 8


def mat_mul(P, Q):
    m, k, l = len(P), len(Q), len(Q[0])
    return [[sum(P[i][a] * Q[a][j] for a in range(k)) for j in range(l)]
            for i in range(m)]


def vec_mat(v, M):
    return [sum(v[a] * M[a][j] for a in range(len(v))) for j in range(len(M[0]))]


def transfer0(A):
    """T(0)[tau][tau'] = sum_{rho > tau} A[tau'][rho]; indices tau+1 = 0..n+1."""
    R = len(A)
    return [[sum(A[t2][rho] for rho in range(R) if rho > t - 1)
             for t2 in range(R)] for t in range(R)]


def brackets(u, N, kmax):
    """c_k = u N^k 1 for k = 0..kmax."""
    out, v = [], u[:]
    for _ in range(kmax + 1):
        out.append(sum(v))
        v = vec_mat(v, N)
    return out


def poly_from_brackets(cs, r):
    return sum(comb(r - 1, k) * c for k, c in enumerate(cs) if k <= r - 1)


def finite_diff_degree(vals):
    """Degree of the polynomial interpolating vals (consecutive r); assumes
    len(vals) exceeds degree + 1."""
    d, seq = 0, vals[:]
    while any(x != 0 for x in seq):
        if all(x == seq[0] for x in seq):
            return d, seq[0]
        seq = [b - a for a, b in zip(seq, seq[1:])]
        d += 1
    return -1, 0  # zero polynomial


def main():
    bad = 0
    for n in range(NMIN, NMAX + 1):
        R = n + 2                    # indices tau = -1..n stored at tau+1
        A = A_from_linusson(n)
        print("=" * 72)
        print("n = %d   (matrix size %dx%d)" % (n, R, R))

        # ---- structural facts S1, S2 --------------------------------------
        s1 = all(A[j + 1][j + 1] == 1 for j in range(0, n + 1))
        s2 = (all(A[j + 1][j] == comb(n, j) - 1 for j in range(1, n + 1))
              and A[1][0] == 0
              and A[0] == [1] + [0] * (R - 1))
        # support check: A[tau][rho] = 0 unless rho <= tau+1
        supp = all(A[t][rho] == 0 for t in range(R) for rho in range(R)
                   if rho > t)      # stored: row t = tau+1, so rho <= tau+1 = t
        print("S1  A[j][j+1] = 1, j=0..n:                  %s" % s1)
        print("S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: %s" % s2)
        print("support rho <= tau+1:                        %s" % supp)
        bad += (not s1) + (not s2) + (not supp)

        # ---- improper -----------------------------------------------------
        T0 = transfer0(A)
        tri = all(T0[t][t2] == 0 for t in range(R) for t2 in range(t))
        unidiag = all(T0[t][t] == 1 for t in range(R))
        N = [[T0[i][j] - (i == j) for j in range(R)] for i in range(R)]
        # N^{n+2} = 0?
        P = [row[:] for row in N]
        for _ in range(R - 1):
            P = mat_mul(P, N)
        nilp = all(x == 0 for row in P for x in row)
        u = [sum(row) for row in A]
        cs = brackets(u, N, R)       # c_0..c_{n+2}
        corner_pred = 1
        for j in range(0, n + 1):
            corner_pred *= comb(n, j)
        print("improper: T(0) upper-triangular %s, unit diagonal %s, "
              "N^%d = 0: %s" % (tri, unidiag, R, nilp))
        print("  c_k = u N^k 1, k=0..%d: %s" % (R, cs))
        top_k = max(k for k, c in enumerate(cs) if c != 0)
        ok_deg = (top_k == n + 1)
        ok_corner = (cs[n + 1] == corner_pred)
        print("  largest nonzero k = %d  (want n+1 = %d): %s"
              % (top_k, n + 1, ok_deg))
        print("  c_{n+1} = %d  (predicted prod_j C(n,j) = %d): %s"
              % (cs[n + 1], corner_pred, ok_corner))
        bad += (not tri) + (not unidiag) + (not nilp) + (not ok_deg) \
            + (not ok_corner)

        # cross-check polynomial against independent ff_count
        rmax = n + 4
        vals_poly = [poly_from_brackets(cs, r) for r in range(1, rmax + 1)]
        vals_ff = [ff_count(n, [0] * r, proper=False)
                   for r in range(1, rmax + 1)]
        match = vals_poly == vals_ff
        deg, lead_top = finite_diff_degree(vals_ff)
        print("  poly vs ff_count, r=1..%d: %s   values %s"
              % (rmax, match, vals_ff))
        print("  finite-difference degree = %d, (n+1)!*lead = %d "
              "(want %d): %s" % (deg, lead_top, corner_pred,
                                 lead_top == corner_pred and deg == n + 1))
        bad += (not match) + (deg != n + 1) + (lead_top != corner_pred)

        # ---- proper -------------------------------------------------------
        Ap = [[0 if rho <= 1 else v for rho, v in enumerate(row)] for row in A]
        T0p = transfer0(Ap)
        cols_zero = all(T0p[t][t2] == 0 for t in range(R) for t2 in (0, 1))
        up = [sum(row) for row in Ap]
        up_supp = up[0] == 0 and up[1] == 0 and up[2] == 1
        # restrict to block tau = 1..n  (stored indices 2..n+1)
        B = [[T0p[i][j] for j in range(2, R)] for i in range(2, R)]
        nB = len(B)                  # = n
        triB = all(B[i][j] == 0 for i in range(nB) for j in range(i))
        unidiagB = all(B[i][i] == 1 for i in range(nB))
        NB = [[B[i][j] - (i == j) for j in range(nB)] for i in range(nB)]
        PB = [row[:] for row in NB]
        for _ in range(nB - 1):
            PB = mat_mul(PB, NB)
        nilpB = all(x == 0 for row in PB for x in row)
        uB = up[2:]
        csp = brackets(uB, NB, nB)
        corner_pred_p = 1
        for j in range(2, n + 1):
            corner_pred_p *= comb(n, j)
        print("proper: cols tau'=-1,0 of T'(0) zero %s; u' supported on "
              "tau>=1 with u'[1]=1 %s" % (cols_zero, up_supp))
        print("  block tau=1..n upper-triangular %s, unit diagonal %s, "
              "N'^%d = 0: %s" % (triB, unidiagB, nB, nilpB))
        print("  c'_k = u' N'^k 1, k=0..%d: %s" % (nB, csp))
        top_kp = max(k for k, c in enumerate(csp) if c != 0)
        ok_degp = (top_kp == n - 1)
        ok_cornerp = (csp[n - 1] == corner_pred_p)
        print("  largest nonzero k = %d  (want n-1 = %d): %s"
              % (top_kp, n - 1, ok_degp))
        print("  c'_{n-1} = %d  (predicted prod_{j>=2} C(n,j) = %d): %s"
              % (csp[n - 1], corner_pred_p, ok_cornerp))
        bad += (not cols_zero) + (not up_supp) + (not triB) \
            + (not unidiagB) + (not nilpB) + (not ok_degp) + (not ok_cornerp)

        vals_polyp = [poly_from_brackets(csp, r) for r in range(1, rmax + 1)]
        vals_ffp = [ff_count(n, [0] * r, proper=True)
                    for r in range(1, rmax + 1)]
        matchp = vals_polyp == vals_ffp
        degp, lead_topp = finite_diff_degree(vals_ffp)
        print("  poly vs ff_count (proper), r=1..%d: %s   values %s"
              % (rmax, matchp, vals_ffp))
        print("  finite-difference degree = %d, (n-1)!*lead = %d "
              "(want %d): %s" % (degp, lead_topp, corner_pred_p,
                                 lead_topp == corner_pred_p
                                 and degp == n - 1))
        bad += (not matchp) + (degp != n - 1) + (lead_topp != corner_pred_p)

    print("=" * 72)
    print("TOTAL mismatches over n = %d..%d: %d" % (NMIN, NMAX, bad))
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
