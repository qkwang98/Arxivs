#!/usr/bin/env python3
"""plot_perron_vs_delta.py -- Figure for article 2's Proposition prop-perron-threshold.

Changelog (newest first):

2026-09-16  Created at Jan's request (item 9): plot lambda(delta) and lambda_pr(delta) for fixed n
            and increasing delta, to sit with Proposition prop-perron-threshold and its Remark
            rem-perron.  The figure's whole point is the PLATEAU: each root climbs and then stops
            dead at its threshold -- delta >= n+1 improper, delta >= n-1 proper -- which is the
            proposition, and the two thresholds are different, which is what the remark explains.

Run (Sage supplies matplotlib here):
    systemd-run --user --scope -p MemoryMax=8G timeout 900 sage code/oneoff/plot_perron_vs_delta.py
"""
import sys
sys.path.insert(0, "/backup/Repositories/ai-workspace/20-projects/exterior-convex/code")
from linusson_ff_counting import A_from_linusson, restrict_proper, transfer_matrix, F

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from sage.all import matrix, QQ, RR


def roots(n, dmax):
    A, Ap = A_from_linusson(n), restrict_proper(A_from_linusson(n))
    out = []
    for d in range(dmax + 1):
        Ti = matrix(QQ, transfer_matrix(A, d, n))
        Tp = matrix(QQ, transfer_matrix(Ap, d, n))
        out.append((d,
                    float(max(RR(abs(e)) for e in Ti.eigenvalues())),
                    float(max(RR(abs(e)) for e in Tp.eigenvalues()))))
    return out


def figure(n, for_print=False):
    dmax = n + 2
    tab = roots(n, dmax)
    Fn = F(n, n)
    Sn = F(n, n) - F(n - 1, n - 1)
    ds = [t[0] for t in tab]
    fig, ax = plt.subplots(figsize=(7.4, 4.6) if for_print else (7.0, 4.4))

    ax.axhline(Fn, color="#1f4e79", lw=1.0, ls=":", zorder=1)
    ax.axhline(Sn, color="#b35806", lw=1.0, ls=":", zorder=1)
    ax.text(dmax + 0.18, Fn, r"$|\mathcal{F}_n|=%d$" % Fn, color="#1f4e79",
            va="center", fontsize=10)
    ax.text(dmax + 0.18, Sn, r"$|S_n|=%d$" % Sn, color="#b35806", va="center", fontsize=10)

    ax.plot(ds, [t[1] for t in tab], "-o", color="#1f4e79", lw=1.7, ms=6,
            label=r"$\lambda(\delta)$  (improper)", zorder=3)
    ax.plot(ds, [t[2] for t in tab], "-s", color="#b35806", lw=1.7, ms=5.5,
            label=r"$\lambda_{\mathrm{pr}}(\delta)$  (proper)", zorder=3)

    # the two thresholds, which are the content of the proposition
    ax.axvline(n + 1, color="#1f4e79", lw=1.0, alpha=0.35)
    ax.axvline(n - 1, color="#b35806", lw=1.0, alpha=0.35)
    ax.annotate(r"$\delta=n+1$", (n + 1, Fn * 0.42), color="#1f4e79", fontsize=10,
                ha="right", rotation=90, va="center")
    ax.annotate(r"$\delta=n-1$", (n - 1, Fn * 0.42), color="#b35806", fontsize=10,
                ha="right", rotation=90, va="center")

    ax.set_xlabel(r"gap $\delta$", fontsize=12)
    ax.set_ylabel("Perron root", fontsize=12)
    ax.set_xticks(ds)
    ax.set_xlim(-0.25, dmax + 1.9)
    ax.set_ylim(0, Fn * 1.10)
    ax.grid(alpha=0.25, lw=0.5)
    ax.legend(loc="lower right", fontsize=10.5, framealpha=0.95)
    if not for_print:
        ax.set_title(r"Perron roots of $T(\delta)$ at $n=%d$: each climbs, then stops at its "
                     r"threshold" % n, fontsize=11)
    fig.tight_layout()
    if for_print:
        out = "../../img/perron-vs-delta-n%d.pdf" % n
        fig.savefig(out, bbox_inches="tight")
    else:
        out = "../../artefacts/perron-vs-delta-n%d.png" % n
        fig.savefig(out, dpi=190)
    plt.close(fig)
    return out, tab, Fn, Sn


for n in (4, 5):
    out, tab, Fn, Sn = figure(n)
    print(out)
    for d, ri, rp in tab:
        print("    delta=%d  improper=%.6f%s  proper=%.6f%s"
              % (d, ri, "  ==|F_n|" if abs(ri - Fn) < 1e-9 else "",
                 rp, "  ==|S_n|" if abs(rp - Sn) < 1e-9 else ""))
print(figure(5, for_print=True)[0])
