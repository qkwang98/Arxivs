"""
Changelog (reverse chronological):
2026-08-09 - Claude: created. Reproduces Kupreyeva (2019)'s Figure 3.1 (T_7^3 = conv(F_7^3)) from
  scratch, for the blog post `blog/posts/kruskal-katona-cauliflower/index.md`'s "picture worth
  staring at" section -- Jan asked to include her actual figure (extracted from the thesis PDF) and
  a SageMath-generated one alongside it, with the shadow function overlaid as a curve on top of the
  red/green scatter (her figure has no such overlay).

  Coordinate convention: her plot's (x,y) = (f_1,f_2) in *dimension* convention (f_1 = number of
  edges, f_2 = number of triangles, for a simplicial complex on p=7 vertices), which is
  ../binomial_basis.py's *cardinality* convention shifted by one: her f_1 = cardinality-2 faces =
  this project's f_2, her f_2 = cardinality-3 faces = this project's f_3. So: x-axis is (this
  project's) f_2 in 0..C(7,2)=21, y-axis is f_3 in 0..kk_shadow_bound(f_2,3), max 35=C(7,3) -- these
  bounds match her figure's axis ranges exactly, confirming the index correspondence. kk_shadow_bound
  is reimplemented locally (plain math.comb) rather than imported from ../binomial_basis.py, since
  that module relies on Sage's global binomial() which isn't in scope for a plain `sage foo.py` run
  without going through Sage's own import/preparse machinery.

  Red = achievable (f_2,f_3) pairs (y <= kk_shadow_bound(x,3), the classical Kruskal-Katona upper
  shadow bound, sufficiency via compressed complexes). Green = integer lattice points strictly
  inside the convex hull of the red points but not themselves achievable -- computed via Sage's
  own Polyhedron, not hand-derived, so the hull is exact rather than assumed. The overlaid curve is
  the shadow bound itself, kk_shadow_bound(x,3) for real x in [0,21] (extended piecewise-constant
  between integers, since the bound is only meaningfully defined at integer x).
"""
from math import comb
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

P = 7  # matches Kupreyeva's T_7^3


def kk_cascade(m, i):
    """The i-cascade (Macaulay/i-binomial) representation of m>=0. Same as ../binomial_basis.py's
    version, reimplemented locally with plain math.comb (that module relies on Sage's global
    binomial(), not importable cleanly into a plain sage-run script's namespace)."""
    terms = []
    remaining = m
    level = i
    a_bound = None
    while remaining > 0 and level >= 1:
        a = level - 1
        while comb(a + 1, level) <= remaining and (a_bound is None or a + 1 < a_bound):
            a += 1
        terms.append((a, level))
        remaining -= comb(a, level)
        a_bound = a
        level -= 1
    assert remaining == 0
    return terms


def kk_shadow_bound(m, i):
    """Kruskal-Katona upper bound on f_i given f_{i-1}=m (cardinality convention, i>=2)."""
    if m == 0:
        return 0
    return sum(comb(a, level + 1) for (a, level) in kk_cascade(m, i - 1))


def main():
    x_max = comb(P, 2)  # 21
    red = [(x, y) for x in range(x_max + 1) for y in range(kk_shadow_bound(x, 3) + 1)]

    hull = Polyhedron(vertices=red)
    lattice_pts = hull.integral_points()
    red_set = set(red)
    green = [tuple(pt) for pt in lattice_pts if tuple(pt) not in red_set]

    fig, ax = plt.subplots(figsize=(7, 5))

    if green:
        gx, gy = zip(*green)
        ax.scatter(gx, gy, marker="o", s=14, color="#2f9e44", label="lattice point, not an f-vector")
    rx, ry = zip(*red)
    ax.scatter(rx, ry, marker="x", s=18, color="#e03131", label="f-vector (achievable)", zorder=3)

    # Piecewise-constant step, evaluated at the floor of each sample point (the bound is only
    # defined at integers; this renders the exact staircase Kruskal-Katona describes).
    curve_x = [x / 4 for x in range(4 * x_max + 1)]
    curve_y = [kk_shadow_bound(int(x), 3) for x in curve_x]
    ax.step(curve_x, curve_y, where="post", color="#1971c2", lw=1.6, alpha=0.85,
            label="shadow function $\\eth_3(x)$", zorder=4)

    ax.set_xlabel("$f_2$ (edges)")
    ax.set_ylabel("$f_3$ (triangles)")
    ax.set_title(f"SageMath reproduction of $T_{P}^3$, shadow function overlaid", fontsize=12)
    ax.legend(fontsize=8, loc="upper left")
    fig.tight_layout()

    out = "/tmp/kupreyeva_repro/kupreyeva-fig31-sage-reproduction.png"
    import os
    os.makedirs(os.path.dirname(out), exist_ok=True)
    fig.savefig(out, dpi=160)
    print("wrote", out)
    print(f"red (f-vectors): {len(red)}, green (hull, non-f-vector): {len(green)}")


main()
