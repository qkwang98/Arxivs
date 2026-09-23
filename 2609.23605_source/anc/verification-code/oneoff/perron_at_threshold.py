#!/usr/bin/env python3
"""perron_at_threshold.py -- is the improper Perron root EXACTLY |F_n| at the threshold?

Changelog (newest first):

2026-09-14  Created while rewriting article 2's Remark 25 (`rem-perron`).  That remark says the
            improper Perron root "tends to |F_n|" as delta -> n+1, while saying the PROPER root
            "equals |S_n| exactly for every delta >= n-1".  The asymmetry looked like an artefact
            rather than mathematics, and it is: `runs/ff-transfer-spectra.md` stops at delta = n,
            one short of the improper threshold delta = n+1 given by Proposition 16, so the
            equality was never computed.  At delta = n the root sits just below |F_n| (552.998 vs
            553 at n = 6), which is exactly what Proposition 16's "the constraint fails for
            exactly one pair" predicts.

            This script computes the missing row.  Prediction, from Proposition 16: for
            delta >= n+1 the constraint tau < rho + delta is vacuous, T(delta) is the all-allowed
            matrix, and the root is |F_n| ON THE NOSE.

Run under the project's guardrail pattern:
    systemd-run --user --scope -p MemoryMax=8G timeout 900 sage code/oneoff/perron_at_threshold.py
"""
import sys, os
sys.path.insert(0, "/backup/Repositories/ai-workspace/20-projects/exterior-convex/code")
from linusson_ff_counting import A_from_linusson, restrict_proper, transfer_matrix, F

from sage.all import matrix, QQ, RR


def roots(n):
    """(|F_n|, |S_n|, [(delta, improper root, proper root)]) for delta up to n+2."""
    A = A_from_linusson(n)
    Ap = restrict_proper(A)
    Fn = F(n, n)                      # |F_n|
    Sn = F(n, n) - F(n - 1, n - 1)    # |S_n|, obs-fnn2
    out = []
    for delta in range(1, n + 3):
        row = []
        for M in (A, Ap):
            T = matrix(QQ, transfer_matrix(M, delta, n))
            ev = [RR(abs(e)) for e in T.eigenvalues()]
            row.append(max(ev))
        out.append((delta, row[0], row[1]))
    return Fn, Sn, out


if __name__ == "__main__":
    print("n  |F_n|  |S_n|   delta  improper-root        proper-root")
    print("   (improper threshold is delta >= n+1; proper is delta >= n-1)")
    for n in range(2, 7):
        Fn, Sn, tab = roots(n)
        for (d, ri, rp) in tab:
            mark_i = "  == |F_n| EXACTLY" if abs(ri - Fn) < 1e-9 else ""
            mark_p = "  == |S_n| EXACTLY" if abs(rp - Sn) < 1e-9 else ""
            print("%d  %5d  %5d    %2d   %18.10f%s   %18.10f%s"
                  % (n, Fn, Sn, d, ri, mark_i, rp, mark_p))
        print()
