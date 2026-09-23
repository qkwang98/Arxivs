# Changelog (reverse chronological):
# 2026-07-30 - Claude: created this file, documenting a Macaulay2 session that
#   uses Amata and Crupi's ExteriorIdeals package to compute and verify the
#   f-vectors of simplicial complexes on 4 vertices, and to numerically
#   confirm Kozlov's simplex theorem for n=4 via a convex-hull computation.

# Hilbert series / f-vector verification (n = 4)

## Goal

Verify computationally, for $n = 4$, the correspondence between Hilbert functions of
quotients $E/I$ of the exterior algebra $E = \bigwedge(k^4)$ by a monomial ideal $I$, and
$f$-vectors of simplicial complexes on 4 vertices — and, restricting to complexes that use all 4
vertices, confirm Kozlov's theorem that their convex hull is a 3-dimensional simplex (Kozlov,
"Convex Hulls of $f$- and $\beta$-Vectors," *Discrete Comput. Geom.* **18**(4) (1997), 421–431).

The tool is Amata and Crupi's Macaulay2 package `ExteriorIdeals` (Amata and Crupi,
"ExteriorIdeals: a package for computing monomial ideals in an exterior algebra," *J. Software
for Algebra and Geometry* **8** (2018), 71–79 — see `../literature/`), whose
`allHilbertSequences` function enumerates every Hilbert sequence of a quotient $E/I$ for $E$ on
$n$ generators, via the Kruskal–Katona–Lindström characterization of such sequences (Aramova,
Herzog, and Hibi, *J. Algebra* **191** (1997), 174–211, cited therein as Theorem 2.6). Since a
monomial ideal $I \subset E$ is automatically squarefree, $E/I$ is the indicator algebra of the
simplicial complex $\Delta = \{\sigma : e_\sigma \notin I\}$, and its Hilbert function
$(h_0, h_1, \dots, h_n)$ *is* the $f$-vector $(f_{-1}, f_0, \dots, f_{n-1})$ of $\Delta$.

## 1. All Hilbert sequences / $f$-vectors for $n = 4$

```
$ M2 -q --no-prompts
loadPackage "ExteriorIdeals"
E = QQ[e_1..e_4, SkewCommutative=>true]
hilbSeqs = allHilbertSequences(E)

o3 = {{1, 4, 6, 4, 1}, {1, 4, 6, 4, 0}, {1, 4, 6, 3, 0}, {1, 4, 6, 2, 0}, {1, 4, 6, 1, 0},
      {1, 4, 6, 0, 0}, {1, 4, 5, 2, 0}, {1, 4, 5, 1, 0}, {1, 4, 5, 0, 0}, {1, 4, 4, 1, 0},
      {1, 4, 4, 0, 0}, {1, 4, 3, 1, 0}, {1, 4, 3, 0, 0}, {1, 4, 2, 0, 0}, {1, 4, 1, 0, 0},
      {1, 4, 0, 0, 0}, {1, 3, 3, 1, 0}, {1, 3, 3, 0, 0}, {1, 3, 2, 0, 0}, {1, 3, 1, 0, 0},
      {1, 3, 0, 0, 0}, {1, 2, 1, 0, 0}, {1, 2, 0, 0, 0}, {1, 1, 0, 0, 0}, {1, 0, 0, 0, 0},
      {0, 0, 0, 0, 0}, {-1, 0, 0, 0, 0}}

#hilbSeqs
o4 = 27
```

The installed package is v1.1 (the paper's Example 3.4, which does this exact computation for
$n=4$, cites v1.0 and reports **25** sequences). The extra two, `{0,0,0,0,0}` (the case $I=E$,
i.e. $E/I = 0$) and `{-1,0,0,0,0}` (a negative first entry, not meaningful as a dimension), are
artifacts of the enumeration: reading `/usr/share/Macaulay2/ExteriorIdeals.m2`, `isHilbertSequence`
only rejects `l#0 > 1`, never `l#0 < 1`, so these two degenerate candidates produced by the
algorithm's borrow-cascade pass validation despite not corresponding to any simplicial complex.
Filtering to `h_0 = 1` recovers the paper's 25 exactly:

```
fVectors = select(hilbSeqs, s -> s#0 == 1)
#fVectors
o6 = 25
```

## 2. Restricting to complexes on all 4 vertices (Kozlov's setting)

Kozlov's theorem concerns $f$-vectors with $(I)_1 = 0$, i.e. $h_1 = n$ — no vertex excluded.
Filtering further:

```
kozlovSeqs = select(fVectors, s -> s#1 == 4)
#kozlovSeqs
o... = 16

netList kozlovSeqs
     (1,4,6,4,1) (1,4,6,4,0) (1,4,6,3,0) (1,4,6,2,0) (1,4,6,1,0) (1,4,6,0,0)
     (1,4,5,2,0) (1,4,5,1,0) (1,4,5,0,0) (1,4,4,1,0) (1,4,4,0,0)
     (1,4,3,1,0) (1,4,3,0,0) (1,4,2,0,0) (1,4,1,0,0) (1,4,0,0,0)
```

## 3. Convex hull: confirming the Kozlov simplex

Dropping the fixed coordinates $h_0=1, h_1=4$, the remaining 16 points $(h_2,h_3,h_4) \in
\mathbb{Z}^3$ are fed to `Polyhedra`'s `convexHull`:

```
needsPackage "Polyhedra"
pts = {{6,4,1},{6,4,0},{6,3,0},{6,2,0},{6,1,0},{6,0,0},
       {5,2,0},{5,1,0},{5,0,0},{4,1,0},{4,0,0},
       {3,1,0},{3,0,0},{2,0,0},{1,0,0},{0,0,0}}
P = convexHull transpose matrix pts

dim P
o5 = 3

numColumns vertices P
o6 = 4

vertices P
o7 = | 0 6 6 6 |
     | 0 0 4 4 |
     | 0 0 0 1 |
```

A $d$-dimensional polytope with exactly $d+1$ vertices is, by definition, a simplex — so this is a
3-simplex, confirming Kozlov's theorem for $n=4$. (This M2 version's `Polyhedra` package has no
`isSimplex` predicate to check directly; the dimension/vertex-count argument suffices.)

The 4 vertices, translated back to full Hilbert sequences $(1,4,h_2,h_3,h_4)$, have a clean
description: they are exactly the $f$-vectors of the $k$-skeleta of the full 3-simplex
$\Delta^3$, for $k = 0, 1, 2, 3$:

| vertex $(h_2,h_3,h_4)$ | Hilbert sequence | skeleton of $\Delta^3$ |
|---|---|---|
| $(0,0,0)$ | $(1,4,0,0,0)$ | 0-skeleton: 4 isolated vertices |
| $(6,0,0)$ | $(1,4,6,0,0)$ | 1-skeleton: complete graph $K_4$ |
| $(6,4,0)$ | $(1,4,6,4,0)$ | 2-skeleton: $\partial \Delta^3$ |
| $(6,4,1)$ | $(1,4,6,4,1)$ | 3-skeleton: $\Delta^3$ itself |

I.e. the Kozlov simplex $\mathcal{P}_n$ is the convex hull of the $f$-vectors of the skeleta of
$\Delta^{n-1}$ — a clean, checkable instance of the general theorem, here for $n=4$.
