#!/usr/bin/env sage
# schlegel_viewpoint_variants.sage
#
# Changelog (newest first):
#
# 2026-09-08  Written so Jan can choose Figure 2's viewpoint by eye rather than by my score.
#             Renders the two n=4 Schlegel diagrams at a spread of viewpoints into
#             img/schlegel-variants/, one PNG per (variant, leg vector), plus a contact sheet.
#
#             The scoring function is the same one used to pick the current (31,-56): the WORSE
#             of the two panels' on-screen relative minimum vertex separation. It is reported
#             beside each variant, but it is only a proxy -- it measures whether vertices collide,
#             not whether the picture reads well, and Jan's own camera scored badly on it while
#             producing the nicest single panel of the lot. That is the whole reason for this
#             script: the metric narrows the field, the eye decides.
#
#             The projection code is duplicated from schlegel_n4_leg_vector_classes.sage rather
#             than imported, because that file writes the real figures and must not change
#             behaviour when this one is edited.

import itertools, math, os
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = "img/schlegel-variants"

def ras(a, d, N):
    return [vector(QQ, [0]*d + [a[j] for j in range(k)] + [0]*(N-d-k)) for k in range(1, len(a)+1)]

def rams(a, degs):
    n = len(a); N = n + max(degs)
    return Polyhedron(vertices=[sum((ras(a, degs[i], N)[t[i]] for i in range(len(degs))),
                                    vector(QQ, [0]*N))
                                for t in itertools.product(range(n), repeat=len(degs))],
                      base_ring=QQ)

def fulldim(P):
    V = [v.vector() for v in P.vertices()]; v0 = V[0]
    B = matrix(QQ, [v - v0 for v in V[1:]]).row_space().basis_matrix()
    return Polyhedron(vertices=[list(B.solve_left(v - v0)) for v in V], base_ring=QQ)

def project(Q, F, eps):
    H = [h for h in Q.Hrepresentation() if h.is_inequality()
         and all(h.eval(v.vector()) == 0 for v in F.vertices())][0]
    u = vector(QQ, H.A()); b = -QQ(H.b())
    cF = sum((v.vector() for v in F.vertices()), vector(QQ, [0]*Q.ambient_dim()))/len(F.vertices())
    p = cF - eps*u
    out = {}
    for v in Q.vertices():
        w = v.vector(); den = u*(w - p)
        if den == 0: return None
        t = (b - u*p)/den
        if t <= 0: return None
        out[tuple(w)] = p + t*(w - p)
    B = matrix(QQ, [list(x) for x in matrix(QQ, [u]).right_kernel().basis()])
    o = list(out.values())[0]
    return {k: tuple(map(float, B.solve_left(x - o))) for k, x in out.items()}

def spread3(pr):
    P = list(pr.values()); m = 1e18
    for i in range(len(P)):
        for j in range(i+1, len(P)):
            m = min(m, math.dist(P[i], P[j]))
    return m/(max(math.dist(a, b) for a in P for b in P) or 1)

def screen_score(pts, elev, azim):
    """Relative minimum vertex separation AS DRAWN, at this viewing angle."""
    e, a = math.radians(elev), math.radians(azim)
    r = (-math.sin(a), math.cos(a), 0.0)
    up = (-math.sin(e)*math.cos(a), -math.sin(e)*math.sin(a), math.cos(e))
    S = [(p[0]*r[0]+p[1]*r[1]+p[2]*r[2], p[0]*up[0]+p[1]*up[1]+p[2]*up[2]) for p in pts]
    mn, mx = 1e18, 0.0
    for i in range(len(S)):
        for j in range(i+1, len(S)):
            d = math.dist(S[i], S[j]); mn = min(mn, d); mx = max(mx, d)
    return mn/(mx or 1)

# (label, elev, azim) -- current figure first, then the metric's other optima, then Jan's camera
VARIANTS = [
    ("current",     31, -56),
    ("low",          8,  58),
    ("high",        53, -180),
    ("nearjan",     41,  28),
    ("side",        54, 125),
    ("jans-camera", 22.2, 16.2),
    ("flat",        14, -56),
    ("steep",       46, -56),
]

CASES = [("all-ones-1111", [1,1,1,1], "#d87a2a"), ("logconcave-1331", [1,3,3,1], "#3a6fd8")]

os.makedirs(OUT, exist_ok=True)
data = {}
for tag, a, col in CASES:
    Q = fulldim(rams(a, [0,1]))
    best = None
    for F in Q.faces(Q.dim()-1):
        for eps in [QQ(1)/2, QQ(1), QQ(2), QQ(4), QQ(8), QQ(16)]:
            pr = project(Q, F, eps)
            if pr is None: continue
            s = spread3(pr)
            if best is None or s > best[0]: best = (s, F, eps, pr)
    _, F, eps, pr = best
    E = [(tuple(e.vertices()[0].vector()), tuple(e.vertices()[1].vector())) for e in Q.faces(1)]
    data[tag] = (pr, E, col)

print(f"{'variant':<14} {'elev':>6} {'azim':>7}   score (worse of the two panels)")
for name, elev, azim in VARIANTS:
    sc = min(screen_score(list(data[t][0].values()), elev, azim) for t, _, _ in CASES)
    print(f"{name:<14} {elev:>6} {azim:>7}   {sc:.4f}")
    for tag, a, col in CASES:
        pr, E, col = data[tag]
        pts = list(pr.values())
        fig = plt.figure(figsize=(5.6, 5.2)); ax = fig.add_subplot(111, projection='3d')
        for (x, y) in E:
            p1, p2 = pr[x], pr[y]
            ax.plot([p1[0], p2[0]], [p1[1], p2[1]], [p1[2], p2[2]], color='k', lw=1.25, alpha=0.85)
        ax.scatter([q[0] for q in pts], [q[1] for q in pts], [q[2] for q in pts],
                   color=col, s=48, depthshade=False, edgecolor='k', linewidth=0.7)
        lo = [min(q[k] for q in pts) for k in range(3)]; hi = [max(q[k] for q in pts) for k in range(3)]
        rng = max(hi[k]-lo[k] for k in range(3)) or 1
        for k, setl in enumerate((ax.set_xlim, ax.set_ylim, ax.set_zlim)):
            mid = (lo[k]+hi[k])/2; setl(mid-rng/2*1.12, mid+rng/2*1.12)
        ax.view_init(elev=elev, azim=azim); ax.set_axis_off()
        try: ax.set_box_aspect((1, 1, 1))
        except Exception: pass
        fig.tight_layout(pad=0.1)
        fig.savefig(f"{OUT}/{name}--{tag}.png", dpi=170, bbox_inches='tight')
        plt.close(fig)
print(f"\nwrote {2*len(VARIANTS)} panels to {OUT}/")
