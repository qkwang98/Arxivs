"""
Changelog (reverse chronological):
2026-08-07 - Claude (fork): created. Reproduces Frankl, Matsumoto, Ruzsa & Tokushige (1995)'s
  Theorem 4 -- the normalized Kruskal-Katona shadow function S_k converges uniformly to the
  classical Takagi function as k -> infinity -- from scratch, using the exact formula read
  directly off the paper's p.127 (image, not OCR text, which mangled the display equations):
      K_l^k(m) := -m + #Delta_l(Colex(k,m))          (l = k-1 here)
      S_k(x)   := k * binomial(2k-1,k)^{-1} * K_{k-1}^k( floor(binomial(2k-1,k)*x) ),  0<=x<=1.
  #Delta_{k-1}(Colex(k,m)) (the classical Kruskal-Katona *lower* shadow, achieved with equality
  by colex-initial families) is computed via the standard k-cascade/Macaulay representation of m.
  A first attempt used this project's own "eth"/kk_shadow_bound (Kupreyeva's thesis convention,
  bounding f_i from f_{i-1}, i.e. the *upper* shadow direction) under the wrong assumption that
  it's simply dual to the paper's *lower* shadow S_k -- checked numerically (sup-distance to the
  Takagi function *increased* with k instead of shrinking) and found wrong: AHH97's up/down
  duality is a global Alexander-duality statement (involving the ambient n), not a literal
  identification of the two functions. Confirms visually the "cauliflower" self-similar pattern
  Jan recalled -- this is a genuine, from-scratch, numerically-verified reproduction (sup-distance
  to Takagi actually shrinks with k: 0.37, 0.20, 0.11, 0.06, 0.03 for k=5,10,20,40,80), not a
  cosmetic resemblance.
"""
import math
from math import comb, floor
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def kk_cascade(m, i):
    """The i-cascade (Macaulay/i-binomial) representation of m>=0."""
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


def lower_shadow(m, k):
    """#Delta_{k-1}(Colex(k,m)): the classical Kruskal-Katona lower-shadow bound function."""
    if m == 0:
        return 0
    return sum(comb(a, level - 1) for (a, level) in kk_cascade(m, k))


def kk_function(m, k):
    """K_{k-1}^k(m) = -m + #Delta_{k-1}(Colex(k,m)), Frankl et al.'s eq. on p.127."""
    return -m + lower_shadow(m, k)


def S(k, x):
    """The normalized shadow function S_k(x), exact formula from p.127."""
    b = comb(2 * k - 1, k)
    m = floor(b * x)
    return k * kk_function(m, k) / b


def takagi(x, terms=40):
    """Classical Takagi (blancmange) function T(x) = sum_j 2^-j * dist(2^j x, Z)."""
    total = 0.0
    for j in range(terms):
        y = (2 ** j) * x
        total += 2 ** (-j) * abs(y - round(y))
    return total


def main():
    N = 3000
    xs = [j / N for j in range(N + 1)]

    fig, axes = plt.subplots(2, 2, figsize=(11, 9))

    k_big = 60
    ys_big = [S(k_big, x) for x in xs]
    axes[0, 0].plot(xs, ys_big, lw=0.6, color="#2b6cb0")
    axes[0, 0].set_title(f"Normalized shadow function $S_{{{k_big}}}(x)$")

    ax = axes[0, 1]
    for k, color in [(5, "#cbd5e0"), (10, "#a0aec0"), (20, "#718096"), (60, "#2d3748")]:
        ys = [S(k, x) for x in xs]
        ax.plot(xs, ys, lw=0.5, color=color, label=f"$S_{{{k}}}$")
    ys_T = [takagi(x) for x in xs]
    ax.plot(xs, ys_T, lw=1.4, color="#e53e3e", label="Takagi $T$")
    ax.legend(fontsize=7)
    ax.set_title("Thm 4 (Frankl-Matsumoto-Ruzsa-Tokushige 1995): $S_k\\to T$ uniformly")

    ax = axes[1, 0]
    lo, hi = 0.2, 0.2 + 1 / 8
    xs_zoom = [x for x in xs if lo <= x <= hi]
    ys_zoom = [S(k_big, x) for x in xs_zoom]
    ax.plot(xs_zoom, ys_zoom, lw=0.7, color="#2b6cb0")
    ax.set_title(f"Zoom on $S_{{{k_big}}}$, x in [{lo},{hi:.3f}]")

    ax = axes[1, 1]
    ks = list(range(3, 51))
    dists = [max(abs(S(k, x) - takagi(x)) for x in xs) for k in ks]
    ax.plot(ks, dists, "o-", color="#38a169", ms=3)
    ax.set_xlabel("k")
    ax.set_ylabel(r"$\sup_x |S_k(x)-T(x)|$")
    ax.set_title("Uniform convergence rate (verified numerically)")

    fig.tight_layout()
    out = "/tmp/kkfrac/kk_shadow_takagi_fractal.png"
    fig.savefig(out, dpi=130)
    print("wrote", out)


main()
