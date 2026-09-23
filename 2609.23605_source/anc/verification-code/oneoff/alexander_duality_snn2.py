#!/usr/bin/env python3
"""alexander_duality_snn2.py

Changelog (reverse chronological):
  2026-09-15  Created. Verification battery for the proposed Alexander-duality
              proof of the open identity |S_n| = F^n(n-2) (article 2,
              Remark obs-fnn2 / open problem 3 of Section 9.2).

              The proposed proof: D(f)(j) := binom(n,j) - f(n-j) is the
              f-vector map induced by Alexander duality
              Delta |-> Delta^v = {sigma : [n] \\ sigma not in Delta},
              an involution on F_n = f-vectors of downward-closed families
              on [n].  Since D(f)(n) = 1 - f(0) and D(f)(n-1) = n - f(1),
              D restricts to a bijection
                  S_n = {f : f(0)=1, f(1)=n}
                    <-->  {g in F_n : top(g) <= n-2},
              and the right-hand set has cardinality F^n(n-2) by the
              embedding identification already used in Lemma lem-joint.

              This script verifies, printing each check with its range:
              (1) recursion level: |S_n| = F^n(n)-F^{n-1}(n-1) == F^n(n-2)
                  for n = 1..30, and the equivalent reduced identity
                  F^n(n-1) - F^n(n-2) == F^{n-1}(n-1) - 1 for n = 2..30,
                  with both sides printed for n = 3..8;
              (2) family level (brute force, n <= 6): D maps F_n into F_n,
                  D is an involution, D(S_n) equals {top <= n-2} as sets,
                  and the statistic conjugation indeg(D(f)) = n - top(f),
                  top(D(f)) = n - indeg(f);
              (3) the reduction bijection: {f in F_n : top(f) = n-1} <-->
                  non-void F_{n-1} via D + support-relabelling, n <= 6;
              (4) persymmetry A[tau][rho] = A[n-rho][n-tau] of the joint
                  (top, indeg) matrix, n <= 8, via the Linusson path.

Run:
  systemd-run --user --scope -p MemoryMax=8G timeout 600 \\
      python3 code/oneoff/alexander_duality_snn2.py
"""

import sys
from math import comb

sys.path.insert(0, "code")
from linusson_ff_counting import (  # noqa: E402
    F, A_from_linusson, brute_fvectors, indeg, top)


def D(f, n):
    """Alexander-dual f-vector: D(f)(j) = binom(n,j) - f(n-j)."""
    return tuple(comb(n, j) - f[n - j] for j in range(n + 1))


def main():
    bad = 0

    # ---- (1) recursion level -------------------------------------------
    print("== (1) Recursion level, n = 1..30 ==")
    for n in range(1, 31):
        Sn = F(n, n) - F(n - 1, n - 1)
        rhs = F(n, n - 2)
        if Sn != rhs:
            bad += 1
            print("MISMATCH |S_%d| = %d  !=  F^%d(%d) = %d"
                  % (n, Sn, n, n - 2, rhs))
    print("|S_n| == F^n(n-2) checked for n = 1..30: %s"
          % ("OK" if bad == 0 else "FAILED"))
    for n in range(2, 31):
        lhs = F(n, n - 1) - F(n, n - 2)
        rhs = F(n - 1, n - 1) - 1
        if lhs != rhs:
            bad += 1
            print("REDUCTION MISMATCH at n = %d: %d != %d" % (n, lhs, rhs))
    print("Reduced identity F^n(n-1)-F^n(n-2) == F^{n-1}(n-1)-1, n = 2..30:"
          " %s" % ("OK" if bad == 0 else "FAILED"))
    print("Explicit values, n = 3..8:")
    for n in range(3, 9):
        print("  n=%d: |S_n|=%d  F^n(n-2)=%d ; reduction LHS=%d RHS=%d"
              % (n, F(n, n) - F(n - 1, n - 1), F(n, n - 2),
                 F(n, n - 1) - F(n, n - 2), F(n - 1, n - 1) - 1))

    # ---- (2) family level, brute force ---------------------------------
    # Predicted enumeration sizes (number of downward-closed families on
    # [n] = Dedekind number D(n)): 2, 3, 6, 20, 168, 7581, 7828354.
    # n <= 6 only; |F_n| (distinct f-vectors) = F^n(n) is far smaller.
    print("\n== (2) Family level, n = 1..6 ==")
    print("Predicted #families to enumerate: D(1..6) ="
          " 3, 6, 20, 168, 7581, 7828354")
    for n in range(1, 7):
        Fn = set(brute_fvectors(n))
        print("n=%d: |F_n| = %d (Linusson F^n(n) = %d)"
              % (n, len(Fn), F(n, n)), end="  ")
        ok = True
        for f in Fn:
            g = D(f, n)
            if g not in Fn:
                ok = False; bad += 1
                print("D(f) NOT in F_n for f =", f)
            if D(g, n) != f:
                ok = False; bad += 1
                print("D not involutive at f =", f)
            if indeg(g, n) != n - top(f) or top(g) != n - indeg(f, n):
                ok = False; bad += 1
                print("statistic conjugation fails at f =", f)
        Sn = {f for f in Fn if f[0] == 1 and f[1] == n}
        Tgt = {g for g in Fn if top(g) <= n - 2}
        if {D(f, n) for f in Sn} != Tgt:
            ok = False; bad += 1
            print("D(S_n) != {top <= n-2} at n =", n)
        print("involution/conjugation/D(S_n)={top<=n-2} (|S_n|=%d): %s"
              % (len(Sn), "OK" if ok else "FAILED"))

    # ---- (3) reduction bijection ---------------------------------------
    print("\n== (3) {top = n-1} <--> non-void F_{n-1}, n = 2..6 ==")
    for n in range(2, 7):
        Fn = set(brute_fvectors(n))
        Ln = {f for f in Fn if top(f) == n - 1}
        img = {D(f, n) for f in Ln}
        # image should be {g in F_n : g(0)=1, g(1) <= n-1}; dropping the
        # forced-zero last coordinate should give exactly non-void F_{n-1}
        ok = all(g[0] == 1 and g[1] <= n - 1 and g[n] == 0 for g in img)
        dropped = {g[:n] for g in img}
        nonvoid = {h for h in brute_fvectors(n - 1) if h[0] == 1}
        ok = ok and (dropped == nonvoid)
        if not ok:
            bad += 1
        print("n=%d: |{top=n-1}| = %d, |non-void F_{n-1}| = %d: %s"
              % (n, len(Ln), len(nonvoid), "OK" if ok else "FAILED"))

    # ---- (4) persymmetry of A ------------------------------------------
    print("\n== (4) A[tau][rho] == A[n-rho][n-tau], n = 1..8 ==")
    for n in range(1, 9):
        A = A_from_linusson(n)  # A[tau+1][rho], tau = -1..n, rho = 0..n+1
        ok = all(A[t + 1][r] == A[n - r + 1][n - t]
                 for t in range(-1, n + 1) for r in range(0, n + 2))
        if not ok:
            bad += 1
        print("n=%d: %s" % (n, "OK" if ok else "FAILED"))

    # ---- (5) gap-reversal invariance of |FF(d)| ------------------------
    # Consequence of the duality: (s_1,...,s_r) |-> (D(s_r),...,D(s_1))
    # bijects chained tuples for gap vector (delta_2,...,delta_r) with
    # chained tuples for the reversed gap vector (delta_r,...,delta_2),
    # since top(D f) = n - indeg(f) and indeg(D f) = n - top(f) turn the
    # chaining constraint around.  With thm-chaining this predicts
    # |FF(d)| (and the proper count, S_n being D-paired with {top<=n-2}
    # -- checked only for the improper count here, since D does NOT map
    # S_n to itself) is invariant under reversing the gaps.
    from linusson_ff_counting import ff_count
    print("\n== (5) |FF| invariance under gap reversal (improper), "
          "n = 2..6 ==")
    gapsets = [(1, 2), (0, 3), (1, 3), (2, 3), (1, 2, 4), (0, 1, 2)]
    for n in range(2, 7):
        ok = True
        for gaps in gapsets:
            ds = [0]
            for g in gaps:
                ds.append(ds[-1] + g)
            dsr = [0]
            for g in reversed(gaps):
                dsr.append(dsr[-1] + g)
            a, b = ff_count(n, ds, False), ff_count(n, dsr, False)
            if a != b:
                ok = False; bad += 1
                print("GAP-REVERSAL MISMATCH n=%d gaps=%s: %d != %d"
                      % (n, gaps, a, b))
        print("n=%d, gap vectors %s and reversals: %s"
              % (n, gapsets, "OK" if ok else "FAILED"))

    print("\nTOTAL mismatches:", bad)
    return bad


if __name__ == "__main__":
    sys.exit(0 if main() == 0 else 1)
