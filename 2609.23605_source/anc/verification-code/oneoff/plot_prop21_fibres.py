#!/usr/bin/env python3
"""plot_prop21_fibres.py -- figures for Proposition 21's fibration (and Proposition 20).

Changelog (newest first):

2026-09-14  Created, after `visualise_prop21_fibres.py` established which projections work.

Reads `artefacts/prop21-fibres-data.json` and draws two figures per n:

  (A) a 3-d layered scatter: the layer axis is f_1 ITSELF, so the slices of Proposition 21 are
      separated exactly rather than by luck of a projection, and the plane is the 2-d projection
      the search found to be injective on every slice at once.  The five vertices of the hull are
      drawn with the edges from e_0, which makes Proposition 20 visible in the same picture: e_0
      sits alone at f_1 = 0 and the other n vertices all lie in the facet f_1 = n, so the body is a
      cone over Koz(n) with apex e_0.

  (B) a graphics array, one panel per slice.  The SAME projection is used in every panel, which is
      what makes them comparable -- and on the slices with k <= 3 it is not a projection at all,
      since f_j = 0 there for j > k, so those panels are exact.

The projection for n = 4 is (f_2, f_3 + f_4), whose second coordinate is just the number of faces of
cardinality at least three; for n = 5 it is (f_2, 3f_3 + 2f_4 + f_5), where the weights are what the
search returned and carry no such reading.
"""
import json, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401

ART = "../../artefacts/"
with open(ART + "prop21-fibres-data.json") as f:
    DATA = json.load(f)

# The search in visualise_prop21_fibres.py orders candidates by coefficient size, so it returns
# the all-negative row before the all-positive one.  They are the same projection up to a
# reflection; take the one that reads upward.
for _k, _d in DATA.items():
    if _d["proj_row2"] and all(c <= 0 for c in _d["proj_row2"]):
        _d["proj_row2"] = [-c for c in _d["proj_row2"]]

# a colour per slice, dark to light, colour-blind safe (viridis sampled)
def colours(m):
    cm = plt.get_cmap("viridis")
    return [cm(0.08 + 0.84 * i / max(1, m - 1)) for i in range(m)]

def project(p, row2):
    """(f_2, sum row2_j f_{j+2}) for a point p = (f_0,...,f_n)."""
    tail = p[2:]
    return tail[0], sum(a * b for a, b in zip(row2, tail))

def label(row2):
    terms = []
    for i, c in enumerate(row2):
        if not c: continue
        j = i + 2
        terms.append(("" if c == 1 else ("-" if c == -1 else str(c))) + "f_%d" % j)
    s = " + ".join(terms)
    return s.replace("+ -", "- ")

def hull_vertices(n):
    """e_0 and the n skeleta F~_j, as full (f_0..f_n) tuples."""
    from math import comb
    e0 = [1] + [0] * n
    verts = [e0]
    for j in range(1, n + 1):
        verts.append([1] + [comb(n, i) if i <= j else 0 for i in range(1, n + 1)])
    return verts

def fig_3d(n, for_print=False):
    d = DATA[str(n)]
    row2, slices = d["proj_row2"], {int(k): v for k, v in d["slices"].items()}
    cols = colours(n + 1)
    fig = plt.figure(figsize=((9.0, 7.4) if for_print else (8.2, 7.0)))
    ax = fig.add_subplot(111, projection="3d")
    # the hull: apex e_0, the facet f_1 = n, and the edges between
    V = hull_vertices(n)
    pe = project(V[0], row2)
    ring = [project(v, row2) for v in V[1:]]
    for (x, y) in ring:
        ax.plot([pe[0], x], [pe[1], y], [0, n], color="0.72", lw=0.8, zorder=1)
    ring_closed = ring + [ring[0]]
    ax.plot([p[0] for p in ring_closed], [p[1] for p in ring_closed], [n] * len(ring_closed),
            color="0.55", lw=1.1, zorder=1)
    for k in range(n + 1):
        pts = [project(p, row2) for p in slices[k]]
        ax.scatter([p[0] for p in pts], [p[1] for p in pts], [k] * len(pts),
                   s=46, color=cols[k], edgecolor="white", linewidth=0.6,
                   depthshade=False, zorder=3,
                   label="$f_1=%d$: $|S_%d|=%d$" % (k, k, len(pts)))
    ax.scatter([pe[0]], [pe[1]], [0], s=120, marker="*", color="#c1272d",
               edgecolor="white", linewidth=0.7, depthshade=False, zorder=4)
    ax.text(pe[0], pe[1], -0.42, "$e_0$", color="#c1272d", ha="center", fontsize=11)
    fs = 15 if for_print else 11
    ax.set_xlabel("$f_2$", labelpad=10, fontsize=fs)
    ax.set_ylabel("$%s$" % label(row2), labelpad=13, fontsize=fs)
    ax.set_zlabel("$f_1$", labelpad=8, fontsize=fs)
    ax.tick_params(labelsize=fs - 3)
    ax.set_zticks(range(n + 1))
    ax.view_init(elev=17, azim=-58)
    if not for_print:                      # in print the LaTeX caption says all of this
        ax.set_title("$S_%d^{+}$ fibred by $f_1$ (Proposition 21), inside the cone over "
                     "$\\mathrm{Koz}(%d)$ (Proposition 20)\n"
                     "%d lattice points; the layer axis is $f_1$ itself, so the slices are exact"
                     % (n, n, sum(len(s) for s in slices.values())), fontsize=10.5, pad=14)
    ax.legend(loc="upper left", fontsize=(12 if for_print else 8.5),
              framealpha=0.92, borderpad=0.7)
    fig.tight_layout()
    if for_print:
        fig.savefig("../../img/prop21-fibres-n4.pdf", bbox_inches="tight")
        plt.close(fig); return "../../img/prop21-fibres-n4.pdf"
    out = ART + "prop21-fibres-3d-n%d.png" % n
    fig.savefig(out, dpi=190); plt.close(fig)
    return out

def fig_array(n):
    d = DATA[str(n)]
    row2, slices = d["proj_row2"], {int(k): v for k, v in d["slices"].items()}
    cols = colours(n + 1)
    allpts = [project(p, row2) for k in slices for p in slices[k]]
    xlo, xhi = min(p[0] for p in allpts), max(p[0] for p in allpts)
    ylo, yhi = min(p[1] for p in allpts), max(p[1] for p in allpts)
    padx, pady = 0.08 * (xhi - xlo + 1), 0.08 * (yhi - ylo + 1)
    ncol = n + 1
    fig, axes = plt.subplots(1, ncol, figsize=(2.5 * ncol, 3.9), sharex=True, sharey=True)
    for k in range(n + 1):
        ax, pts = axes[k], [project(p, row2) for p in slices[k]]
        # every earlier slice, faint, to show the nesting
        for j in range(k):
            q = [project(p, row2) for p in slices[j]]
            ax.scatter([p[0] for p in q], [p[1] for p in q], s=16, color="0.86", zorder=1)
        ax.scatter([p[0] for p in pts], [p[1] for p in pts], s=44, color=cols[k],
                   edgecolor="white", linewidth=0.5, zorder=3)
        dim = max(0, k - 1)          # measured in visualise_prop21_fibres.py
        ax.set_title("$f_1=%d$   $|S_%d|=%d$\n%s" %
                     (k, k, len(pts),
                      "exact (dim %d)" % dim if dim <= 2 else "projected (dim %d)" % dim),
                     fontsize=9.5)
        ax.set_xlim(xlo - padx, xhi + padx); ax.set_ylim(ylo - pady, yhi + pady)
        ax.set_xlabel("$f_2$", fontsize=9)
        ax.grid(alpha=0.22, lw=0.5); ax.set_aspect("equal", adjustable="box")
        if k == 0: ax.set_ylabel("$%s$" % label(row2), fontsize=9)
    fig.suptitle("Proposition 21 slice by slice: $S_{%d}^{+}=\\bigsqcup_{k=0}^{%d}\\iota_k(S_k)$"
                 "   (grey = the earlier slices, for the nesting)" % (n, n), fontsize=11)
    fig.tight_layout(rect=(0, 0, 1, 0.93))
    out = ART + "prop21-fibres-array-n%d.png" % n
    fig.savefig(out, dpi=190); plt.close(fig)
    return out

if __name__ == "__main__":
    for n in (4, 5):
        print("n = %d:" % n)
        print("   ", fig_3d(n))
        print("   ", fig_array(n))
