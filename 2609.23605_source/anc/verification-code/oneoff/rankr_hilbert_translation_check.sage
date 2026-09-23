# Changelog (reverse chronological):
# 2026-08-06 - Claude: created, generalizing rank2_hilbert_translation_check.sage
#   to general r. Checks the conjectured correction R + sum_{i=2}^r e_{d_i}
#   (see ../artefacts/right-angle-simplices-notes.md's rank-2 section) against
#   a *directly computed* true-Hilbert-function polytope (not derived from the
#   naive sum + assumed correction, but built from scratch via each
#   generator's own f_0=1 bump), for r=3, including a tied-degree case
#   (d_2=d_3) to check the correction's multiplicity handling.

def kozlov_vector(n):
    return [binomial(n, k) for k in range(1, n + 1)]

def right_angle_vertices(a):
    n = len(a)
    return [list(a[:i]) + [0] * (n - i) for i in range(1, n + 1)]

def pad(v, N):
    v = list(v)
    return v + [0] * (N - len(v))

def shift_naive(v, d, N):
    return [0] * d + list(v) + [0] * (N - d - len(v))

def trueshift(h, d, N):
    # Ambient Hilbert-function contribution of a generator of degree d whose
    # E/I has rank-1 Hilbert function h (h[k] = H(k+1), k=0..n-1): puts a
    # genuine "1" at ambient degree d (from H(0)=1, the surviving generator
    # itself) instead of the naive shift's wrongly-zeroed entry there.
    n = len(h)
    v = [0] * N
    if d >= 1:
        v[d - 1] = 1
    for k in range(n):
        v[d + k] = h[k]
    return v

def unit(k, N):
    e = [0] * N
    e[k - 1] = 1
    return e

def check(n, degs):
    assert degs[0] == 0
    r = len(degs)
    a = kozlov_vector(n)
    F1 = right_angle_vertices(a)  # vertices of conv(achievable rank-1 Hilbert fns) = kozlov_simplex(n)
    N = n + max(degs)

    # R = sum_i shift^{d_i}(angle(a)), exactly as right_angle_minkowski_sum builds it
    R = Polyhedron(vertices=[pad(F1[0], N)])  # seed with a point, replaced below
    polys = [Polyhedron(vertices=[shift_naive(v, d, N) for v in F1]) for d in degs]
    R = polys[0]
    for P in polys[1:]:
        R = R + P

    # naive vertex-tuple sums (tautologically should equal R)
    from itertools import product
    naive_pts = []
    direct_pts = []
    for hs in product(F1, repeat=r):
        naive_pts.append([sum(shift_naive(hs[i], degs[i], N)[k] for i in range(r)) for k in range(N)])
        direct_pts.append([sum(trueshift(hs[i], degs[i], N)[k] for i in range(r)) for k in range(N)])

    S_naive = Polyhedron(vertices=naive_pts)
    S_direct = Polyhedron(vertices=direct_pts)  # ground truth: true Hilbert functions, from scratch

    correction = [0] * N
    for d in degs[1:]:
        correction[d - 1] += 1
    R_corrected = R + Polyhedron(vertices=[correction])

    return dict(
        n=n, degs=degs, correction=correction,
        R_eq_Snaive=(R == S_naive),
        R_eq_Sdirect=(R == S_direct),
        Rcorrected_eq_Sdirect=(R_corrected == S_direct),
        R_nverts=R.n_vertices(), Sdirect_nverts=S_direct.n_vertices(),
    )

for row in [check(5, (0, 1, 2)), check(5, (0, 2, 2)), check(4, (0, 1, 1, 2))]:
    print(row)
