#!/usr/bin/env sage
# fig_summands_and_sum_n3.sage
#
# Changelog (newest first):
#
# 2026-09-07  Written to join the manuscript's Figures 1 and 2 into one, at Jan's request, so the
#             figure reads "summand + summand = sum" rather than leaving the reader to pair up two
#             separate figures. Supersedes the ad-hoc commands that produced
#             img/minkowski-{all-ones-111,kozlov-like-121}.png and img/summands-n3.png -- those were
#             generated interactively and never saved, contrary to the project's own convention
#             that figure code lives in code/. This script regenerates ALL SIX panels from one
#             place, which is also the only way to guarantee they share a viewpoint and a scale;
#             a "+ ... = " figure whose panels are drawn at different scales would be misleading.
#
#             Two deliberate choices:
#             (1) Rendering is matplotlib, not Sage's .show(). Sage's 3D output was the source of an
#                 earlier error in this project (a "Schlegel projection" that was really a shadow),
#                 and here the viewpoint and the axis limits must be pinned exactly, which
#                 matplotlib lets us state outright.
#             (2) The bounding box is shared per ROW (per leg vector), not globally: a=(1,2,1)
#                 spans x2 in [0,3] where a=(1,1,1) spans [0,2], and forcing one global box would
#                 shrink the all-ones row for no gain. Within a row -- which is where the
#                 "+ = " reading happens -- the scale is identical across all three panels.

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import sys, os

sys.path.insert(0, "../")
load("../right_angle_simplex.py")

N_ = 3
D_ = 1
ELEV, AZIM = 22, -58
OUTDIR = "../../img"

CASES = [
    ("ones", [1, 1, 1], r"$\vec a=(1,1,1)$"),
    ("logconc", [1, 2, 1], r"$\vec a=(1,2,1)$"),
]

def drop_x1(P):
    """Project away the constant coordinate x_1; returns a polytope in R^3."""
    return Polyhedron(vertices=[list(v)[1:4] for v in P.vertices_list()])

def panels(a):
    n, d = len(a), D_
    N = n + d
    S1 = pad_polytope(right_angle_simplex(a), N)
    S2 = pad_polytope(shift_polytope(right_angle_simplex(a), d), N)
    R = right_angle_minkowski_sum(a, [0, d])
    return [drop_x1(S1), drop_x1(S2), drop_x1(R)]

def render(P, path, box, color):
    fig = plt.figure(figsize=(3.2, 3.0))
    ax = fig.add_subplot(111, projection="3d")
    verts = [[float(c) for c in v] for v in P.vertices_list()]

    # 2-faces: for the 3-dimensional sum these are its facets; for a 2-dimensional
    # summand triangle there is exactly one, the triangle itself.
    faces = []
    for f in P.faces(2):
        fv = [[float(c) for c in v] for v in f.vertices()]
        if len(fv) >= 3:
            faces.append(order_cycle(fv))
    if not faces and len(verts) == 3:
        faces = [verts]

    pc = Poly3DCollection(faces, alpha=0.32, facecolor=color,
                          edgecolor="0.15", linewidths=1.3)
    ax.add_collection3d(pc)
    xs, ys, zs = zip(*verts)
    ax.scatter(xs, ys, zs, s=14, c="0.1", depthshade=False)

    (x0, x1), (y0, y1), (z0, z1) = box
    ax.set_xlim(x0, x1); ax.set_ylim(y0, y1); ax.set_zlim(z0, z1)
    ax.set_box_aspect((x1 - x0, y1 - y0, z1 - z0))
    ax.view_init(elev=ELEV, azim=AZIM)
    ax.set_xlabel("$x_2$", labelpad=-6); ax.set_ylabel("$x_3$", labelpad=-6)
    # z sits on the right-hand edge; a negative labelpad here pushed "$x_4$" clean off the canvas.
    # Matplotlib places the z-label off-canvas here at every labelpad tried, positive or
    # negative, so it is positioned explicitly in axes fractions instead.
    ax.set_zlabel("")
    ax.text2D(0.90, 0.80, "$x_4$", transform=ax.transAxes, fontsize=10)
    ax.tick_params(labelsize=6, pad=-3)
    ax.set_xticks(range(int(x0), int(x1) + 1))
    ax.set_yticks(range(int(y0), int(y1) + 1))
    ax.set_zticks(range(int(z0), int(z1) + 1))
    fig.subplots_adjust(left=0.04, right=0.88, top=0.99, bottom=0.01)
    fig.savefig(path, dpi=220, transparent=True)
    plt.close(fig)

def order_cycle(fv):
    """Order a planar face's vertices into a boundary cycle (matplotlib fills in given order)."""
    import numpy as np
    P = np.array(fv, dtype=float)
    c = P.mean(axis=0)
    Q = P - c
    u, s, vt = np.linalg.svd(Q)
    e1, e2 = vt[0], vt[1]
    ang = np.arctan2(Q @ e2, Q @ e1)
    return [fv[i] for i in np.argsort(ang)]

os.makedirs(OUTDIR, exist_ok=True)
for key, a, _lab in CASES:
    ps = panels(a)
    R = ps[2]
    # The box must cover ALL THREE panels, not just the sum: the unshifted summand sits at
    # x_2 in [0,1] while the sum spans [1,2], so a box taken from the sum alone would render
    # the first summand clipped and outside its own frame.
    vs = [[float(c) for c in v] for p in ps for v in p.vertices_list()]
    box = tuple((min(v[i] for v in vs), max(v[i] for v in vs)) for i in range(3))
    print(f"{key}: a={a}  box={box}  dims={[p.dim() for p in ps]}  "
          f"verts={[p.n_vertices() for p in ps]}  facets_of_sum={R.n_facets()}")
    for tag, P, col in zip(("s1", "s2", "sum"), ps,
                           ("#4878a8", "#a85c48", "#6b8f5a")):
        render(P, f"{OUTDIR}/msum-n3-{key}-{tag}.png", box, col)
        print(f"    wrote {OUTDIR}/msum-n3-{key}-{tag}.png")
print("done")
