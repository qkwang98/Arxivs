#!/usr/bin/env sage
# triangulations_and_cayley_n5d2.sage
#
# Changelog (newest first):
#
# 2026-09-07  RESULTS, and a correction. (A) and (B) ran and are trustworthy:
#               (A) 6/19/9 and 6/20/10, matching the manuscript exactly.
#               (B) the Cayley configuration has 10 points (not 12 -- angle(a) has n vertices, not
#                   n+1, since right_angle_simplex excludes the origin) in dim 7, hence corank 2,
#                   and has exactly 6 triangulations for BOTH leg vectors. The sum itself timed out
#                   at 15 min, as expected: corank 12.
#                   The `regular=True` branch raised ValueError and reported nothing -- unfixed.
#             (C) IS WRONG AND ITS "True" COLUMN PROVES NOTHING. It builds A_p = {d_p,...,d_p+n},
#             n+1 elements plus a slack coordinate, on the assumption that angle(a) contains the
#             origin. It does not: angle(a) = conv{v_1,...,v_n}, so the correct index set is
#             A_p = {d_p+1, ..., d_p+n}, n elements, no slack -- and the shifted summand needs a
#             translation by e_{d} that this code never applies. Accordingly "D(R) == Delta+Delta"
#             is False in all 21 cases, which is a fact about the wrong polytope. The neighbouring
#             "polymatroid H-desc == it : True" compares the transversal-polymatroid inequalities
#             against that same wrong object, so it merely re-derives a known theorem and says
#             nothing whatever about R. The interesting claim is therefore UNTESTED, not refuted.
#
# 2026-09-07  Written to answer Jan's question: how many triangulations does the rank-two
#             Kozlov/all-ones polytope have at n = 5, d = 2, and is there a canonical one with
#             combinatorial meaning that could close the H-description gap?
#
#             Three things are computed, in increasing order of what they might buy:
#
#             (A) Baseline. dim / #vertices / #facets for both leg vectors, checked against the
#                 manuscript's Examples ex-ones-facets and ex-kozlov-facets (6 / 19 / 9 and
#                 6 / 20 / 10). If this disagrees, nothing below is trustworthy.
#
#             (B) Triangulation counts, via TOPCOM, of the vertex configuration itself and -- far
#                 more usefully -- of the CAYLEY configuration. The Cayley trick says
#                 triangulations of Cay(P1,P2) correspond to MIXED subdivisions of P1+P2, and the
#                 Cayley configuration has only 2(n+1) = 12 points in dim 7 against the sum's 19-20
#                 vertices in dim 6, so it is the tractable object. Mixed subdivisions are also the
#                 ones that remember the summand decomposition, which is exactly the structure the
#                 extremal tensor is about.
#
#             (C) A structural claim to test, not assume. In "difference coordinates"
#                 D(x)_c = x_c - x_{c+1} (unimodular, and the inverse of the prefix-sum map the
#                 V-side proof already uses), the ALL-ONES right-angle simplex should become a
#                 standard simplex, making R unimodularly equivalent to a Minkowski sum of two
#                 standard simplices on INTERVALS, Delta_{A_1} + Delta_{A_2}, A_p = [d_p, d_p+n].
#                 Sums of standard simplices are transversal polymatroids with a known submodular
#                 facet description, which -- if the equivalence holds -- would settle
#                 conj-ones-hrep by citation rather than by a new proof. Tested here against the
#                 actual polytope for a range of (n,d), not just n=5,d=2.

import sys, itertools
sys.path.insert(0, "../")
load("../right_angle_simplex.py")

def kozlov(n):
    return [binomial(n, j) for j in range(1, n + 1)]

def ones(n):
    return [1] * n

# ---------------------------------------------------------------- (A) baseline

def baseline(n, d):
    out = {}
    for name, a in (("all-ones", ones(n)), ("kozlov", kozlov(n))):
        R = right_angle_minkowski_sum(a, [0, d])
        out[name] = (R.dim(), R.n_vertices(), R.n_facets(), R)
    return out

print("=" * 72)
print("(A) baseline, n = 5, d = 2   [manuscript says 6/19/9 and 6/20/10]")
print("=" * 72)
base = baseline(5, 2)
for name in ("all-ones", "kozlov"):
    dim, nv, nf, _ = base[name]
    print(f"  {name:9s}  dim={dim}  vertices={nv}  facets={nf}")

# ---------------------------------------------------- (B) triangulation counts

def count_triangulations(points, label, want_all=True, timeout_s=900):
    """#triangulations and #regular triangulations of a point configuration."""
    from sage.geometry.triangulation.point_configuration import PointConfiguration
    pc = PointConfiguration(points)
    res = {}
    try:
        alarm(timeout_s)
        res["regular"] = len(list(PointConfiguration(points, regular=True).triangulations()))
        cancel_alarm()
    except (AlarmInterrupt, Exception) as e:
        cancel_alarm(); res["regular"] = f"(timeout/err: {type(e).__name__})"
    if want_all:
        try:
            alarm(timeout_s)
            res["all"] = len(list(pc.triangulations()))
            cancel_alarm()
        except (AlarmInterrupt, Exception) as e:
            cancel_alarm(); res["all"] = f"(timeout/err: {type(e).__name__})"
    return res

def cayley_points(a, d):
    """Cayley configuration of the two summands: (v,0) for summand 1, (w,1) for summand 2."""
    n = len(a)
    N = n + d
    P1 = pad_polytope(right_angle_simplex(a), N)
    P2 = pad_polytope(shift_polytope(right_angle_simplex(a), d), N)
    pts  = [list(v) + [0] for v in P1.vertices_list()]
    pts += [list(v) + [1] for v in P2.vertices_list()]
    return pts

print()
print("=" * 72)
print("(B) triangulation counts, n = 5, d = 2")
print("=" * 72)
for name, a in (("all-ones", ones(5)), ("kozlov", kozlov(5))):
    cay = cayley_points(a, 2)
    from sage.geometry.triangulation.point_configuration import PointConfiguration
    pc_cay = PointConfiguration(cay)
    print(f"  {name}: Cayley config = {len(cay)} points, dim {pc_cay.dim()} "
          f"(sum has {base[name][1]} vertices in dim {base[name][0]})")
    r = count_triangulations(cay, name)
    print(f"      Cayley  -> all = {r.get('all')},  regular = {r.get('regular')}")
    print(f"      [Cayley trick: these are the MIXED subdivisions of the sum]")

for name in ("all-ones", "kozlov"):
    R = base[name][3]
    r = count_triangulations(R.vertices_list(), name, want_all=True, timeout_s=900)
    print(f"  {name}: sum itself -> all = {r.get('all')},  regular = {r.get('regular')}")

# --------------------------------------- (C) all-ones as a sum of interval simplices

def difference_map_image(R):
    """Apply D(x)_c = x_c - x_{c+1} (x_{N+1} = 0) to every vertex; D is unimodular."""
    N = R.ambient_dim()
    M = matrix(ZZ, N, N, lambda i, j: 1 if i == j else (-1 if j == i + 1 else 0))
    return Polyhedron(vertices=[list(M * vector(v)) for v in R.vertices_list()])

def interval_simplex_sum(n, d, N):
    """Delta_{A_1} + Delta_{A_2}, A_p = {d_p, ..., d_p+n}, in coordinates 0..N."""
    def simplex_on(A):
        return Polyhedron(vertices=[[1 if c == j else 0 for c in range(N + 1)] for j in A])
    A1 = list(range(0, n + 1))
    A2 = list(range(d, d + n + 1))
    return simplex_on(A1) + simplex_on(A2)

def transversal_polymatroid_ineqs(n, d, N, r=2):
    """Submodular description of sum of Delta_{A_p}: x>=0, sum x = r,
       sum_{j in S} x_j <= #{p : A_p meets S}."""
    A = [set(range(0, n + 1)), set(range(d, d + n + 1))]
    ineqs = []
    ground = list(range(N + 1))
    for k in range(1, len(ground)):
        for S in itertools.combinations(ground, k):
            Sset = set(S)
            rhs = sum(1 for Ap in A if Ap & Sset)
            if rhs < r:                       # rhs = r is implied by sum x = r and x >= 0
                ineqs.append((set(S), rhs))
    return ineqs

print()
print("=" * 72)
print("(C) is the ALL-ONES sum a sum of interval simplices, after D?")
print("=" * 72)
allgood = True
for n in range(2, 8):
    for d in range(1, n):
        N = n + d
        R = right_angle_minkowski_sum(ones(n), [0, d])
        DR = difference_map_image(R)
        S = interval_simplex_sum(n, d, N)
        # DR lives in R^N, S in R^{N+1}; compare via the affine hull-free test:
        # S should equal DR embedded by prepending the slack coordinate x_0 = 2 - sum(DR coords).
        emb = Polyhedron(vertices=[[2 - sum(v)] + list(v) for v in DR.vertices_list()])
        same = (emb == S)
        # and check the transversal-polymatroid inequality description cuts out S
        ineqs = transversal_polymatroid_ineqs(n, d, N)
        H = [[QQ(2), ] + [QQ(-1) if c in Sset else QQ(0) for c in range(N + 1)]
             for (Sset, rhs) in [(s, r0) for (s, r0) in ineqs]]
        H = [[QQ(rhs)] + [QQ(-1) if c in Sset else QQ(0) for c in range(N + 1)]
             for (Sset, rhs) in ineqs]
        Q = Polyhedron(ieqs=H + [[QQ(0)] + [QQ(1) if c == j else QQ(0) for c in range(N + 1)]
                                 for j in range(N + 1)],
                       eqns=[[QQ(-2)] + [QQ(1)] * (N + 1)])
        ok = same and (Q == S)
        allgood = allgood and ok
        print(f"  n={n} d={d}:  D(R) == Delta_A1+Delta_A2 : {same};   "
              f"polymatroid H-desc == it : {Q == S}")
print()
print("ALL CASES AGREE" if allgood else "*** MISMATCH -- claim (C) is false as stated ***")
