# verify_section8_restated.sage -- check §8's RESTATED results against exact polyhedral
# computation, in the unified 1-indexed convention introduced 2026-09-10.
#
# Changelog (newest first):
#
# 2026-09-10  Created. §8 was rewritten that day: Proposition 47 (prop-kozlov-partial) was split
#             into four propositions with explicit hypotheses, prop-regimes into three, and both
#             extremal-matrix theorems were restated in ONE index base (indices 1..n on every
#             axis; thm-ones had been 1-indexed and thm-kozlov-matrix 0-indexed). The index
#             translation is exactly the kind of edit that silently inverts a claim, so every
#             restated statement is re-verified here from scratch against Sage's exact rational
#             polyhedral arithmetic rather than trusted.
#
#             Ground truth throughout: M[i][j] = 1 iff v_i + u_j is a vertex of the Minkowski sum,
#             computed by building the sum as the convex hull of all n^2 pairwise sums and asking
#             Sage for its vertex list.
#
# Run:  sage code/oneoff/verify_section8_restated.sage

from itertools import product

def legs(kind, n):
    if kind == "ones":
        return [1] * n
    if kind == "kozlov":
        return [binomial(n, k) for k in range(1, n + 1)]
    if kind == "random":
        set_random_seed(20260910 + n)
        return [ZZ.random_element(1, 12) for _ in range(n)]
    raise ValueError(kind)

def vertex_sets(a, n, d):
    """Return (V, U): vertices of the two summands in R^N, N = n+d, 1-indexed lists."""
    N = n + d
    V = [vector(QQ, [a[c] if c < k else 0 for c in range(N)]) for k in range(1, n + 1)]
    U = [vector(QQ, [a[c - d] if d < c + 1 <= d + k else 0 for c in range(N)])
         for k in range(1, n + 1)]
    return V, U

def true_matrix(a, n, d):
    """M[i][j] for 1 <= i,j <= n, as a dict keyed by (i,j)."""
    V, U = vertex_sets(a, n, d)
    pts = {}
    for i in range(1, n + 1):
        for j in range(1, n + 1):
            pts[(i, j)] = V[i - 1] + U[j - 1]
    P = Polyhedron(vertices=[tuple(p) for p in pts.values()], base_ring=QQ)
    verts = set(tuple(v) for v in P.vertices_list())
    return {k: (1 if tuple(p) in verts else 0) for k, p in pts.items()}, P

# ---------------------------------------------------------------- the restated formulas

def formula_ones(n, d, i, j):
    """thm-ones, as restated: 0 iff 1<=t<=m, 1<=j<=m, t != j."""
    m, t = n - d, i - d
    return 0 if (1 <= t <= m and 1 <= j <= m and t != j) else 1

def formula_kozlov(n, d, i, j):
    """thm-kozlov-matrix, as restated: 0 iff 1<=t<=m, 1<=j<=m, and (j<t or j==t+1)."""
    m, t = n - d, i - d
    return 0 if (1 <= t <= m and 1 <= j <= m and (j < t or j == t + 1)) else 1

fails = []
def check(cond, msg):
    if not cond:
        fails.append(msg)

# ---------------------------------------------------------------- 1. the two theorems

print("=== thm-ones (48) and thm-kozlov-matrix (59), restated 1-indexed ===")
for n in range(2, 8):
    for d in range(1, n):
        m = n - d
        for kind, formula in (("ones", formula_ones), ("kozlov", formula_kozlov)):
            a = legs(kind, n)
            M, P = true_matrix(a, n, d)
            bad = [(i, j) for (i, j) in M if M[(i, j)] != formula(n, d, i, j)]
            check(not bad, f"{kind} n={n} d={d}: formula disagrees at {bad[:4]}")
            nv = sum(M.values())
            want = n^2 - m * (m - 1) if kind == "ones" else n^2 - (m - 1) * (m + 2) / 2
            check(nv == want, f"{kind} n={n} d={d}: count {nv} != {want}")
            check(len(P.vertices_list()) == nv,
                  f"{kind} n={n} d={d}: polytope has {len(P.vertices_list())} vertices, matrix says {nv}")
    print(f"  n={n}: ok")

# ------------------------------------------------- 2. the three regime propositions (44,45,46)

print("=== prop-regimes-tie / -disjoint / -boundary (44,45,46), any positive leg vector ===")
for n in range(1, 7):
    for kind in ("ones", "kozlov", "random"):
        a = legs(kind, n)
        M, _ = true_matrix(a, n, 0)                                   # tie: d = 0
        check(all(M[(i, j)] == (1 if i == j else 0) for i in range(1, n + 1)
                  for j in range(1, n + 1)),
              f"prop-regimes-tie n={n} {kind}: not the identity matrix")
        M, _ = true_matrix(a, n, n)                                   # disjoint: d = n
        check(all(v == 1 for v in M.values()),
              f"prop-regimes-disjoint n={n} {kind}: not all ones")
        if n >= 2:                                                    # boundary: d = n-1
            M, _ = true_matrix(a, n, n - 1)
            check(all(v == 1 for v in M.values()),
                  f"prop-regimes-boundary n={n} {kind}: not all ones")
            check(sum(M.values()) == n^2, f"prop-regimes-boundary n={n} {kind}: count")
    print(f"  n={n}: ok")

# ------------------------------------- 3. the four split propositions (53,54,55,56) separately

print("=== prop-outside-block (53), prop-diagonal (54), prop-adjacent (55) -- ANY positive a ===")
for n in range(2, 7):
    for d in range(1, n):
        m = n - d
        for kind in ("ones", "kozlov", "random"):
            a = legs(kind, n)
            M, _ = true_matrix(a, n, d)
            for i in range(1, n + 1):
                t = i - d
                for j in range(1, n + 1):
                    if i <= d or j > m:                                        # 53
                        check(M[(i, j)] == 1, f"53 fails {kind} n={n} d={d} ({i},{j})")
                    if 1 <= t <= m and j == t:                                 # 54
                        check(M[(i, j)] == 1, f"54 fails {kind} n={n} d={d} ({i},{j})")
                    if 1 <= t <= m and 1 <= j <= m and abs(j - t) == 1:        # 55
                        check(M[(i, j)] == 0, f"55 fails {kind} n={n} d={d} ({i},{j})")
    print(f"  n={n}: ok")

print("=== prop-below-diagonal (56) and prop-gapK (57) -- need the rho hypothesis ===")
for n in range(2, 8):
    for d in range(1, n):
        m = n - d
        a = legs("kozlov", n)
        rho = lambda s: QQ(binomial(n, d + s)) / QQ(binomial(n, s))
        M, _ = true_matrix(a, n, d)
        for i in range(1, n + 1):
            t = i - d
            for j in range(1, n + 1):
                if 1 <= t <= m and 1 <= j < t:                                 # 56
                    check(M[(i, j)] == 0, f"56 fails n={n} d={d} ({i},{j})")
                if 1 <= t <= m and 1 <= j <= m and j - t >= 2:                 # 57
                    check(rho(t + 1) > rho(j), f"57 hypothesis rho_(t+1)>rho_j fails n={n} d={d} ({i},{j})")
                    check(M[(i, j)] == 1, f"57 fails n={n} d={d} ({i},{j})")
    print(f"  n={n}: ok")

# ------------------------------------------------- 4. lem-binomial-ratio (52), stated ranges

print("=== lem-binomial-ratio (52): positivity range and strict decrease on 1..m ===")
for n in range(1, 12):
    for d in range(1, n + 1):
        m = n - d
        rho = [QQ(binomial(n, d + s)) / QQ(binomial(n, s)) for s in range(1, n + 1)]
        for s in range(1, n + 1):
            check((rho[s - 1] > 0) == (s <= m), f"52(1) fails n={n} d={d} s={s}")
        for s in range(1, m + 1):
            check(rho[s - 1] > rho[s], f"52(2) fails n={n} d={d} s={s}")
        # and the claim that strictness genuinely fails beyond m
        for s in range(m + 2, n):
            check(rho[s - 1] == rho[s] == 0, f"52 tail fails n={n} d={d} s={s}")
print("  ok")

# --------------------------------------------- 5. the two concrete claims made in the prose

print("=== prose claims: the prop-adjacent counterexample, and the all-ones/Kozlov differences ===")
# prop-adjacent's hypothesis j <= m is load-bearing exactly at t = m, i.e. at (i,j) = (n, m+1):
# there j = t+1 leaves the shared block and prop-outside-block gives a ONE.  Check the general
# claim, not just the n=5 instance quoted in the prose.
for n in range(2, 8):
    for d in range(1, n):
        m = n - d
        Mk, _ = true_matrix(legs("kozlov", n), n, d)
        if m + 1 <= n:
            check(Mk[(n, m + 1)] == 1,
                  f"n={n} d={d}: entry (n,m+1)=({n},{m+1}) should be ONE (prop-outside-block)")
check(true_matrix(legs("kozlov", 5), 5, 1)[0][(5, 5)] == 1,
      "the (n,d,i,j)=(5,1,5,5) entry cited in the prose as a ONE is not one")
for d, want in ((1, [(2, 3), (2, 4), (3, 4)]), (2, [(3, 3)]), (3, [])):
    Mo, _ = true_matrix(legs("ones", 5), 5, d)
    Mk, _ = true_matrix(legs("kozlov", 5), 5, d)
    diff = sorted(k for k in Mo if Mo[k] != Mk[k])
    check(diff == want, f"n=5 d={d}: differences {diff} != {want}")
    check(len(diff) == binomial(5 - d - 1, 2), f"n=5 d={d}: count != binom(m-1,2)")
print("  ok")

print()
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails[:40]:
        print("  " + f)
else:
    print("ALL CHECKS PASSED")
