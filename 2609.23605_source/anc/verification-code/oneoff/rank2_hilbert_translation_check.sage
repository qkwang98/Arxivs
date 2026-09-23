# Changelog (reverse chronological):
# 2026-08-06 - Claude: created. Checks the TEXIMG-9 "candidate theorem"
#   (session-images-2026-08-06-1156.org, top-level transcripts/) against
#   the n=6 data already in ../artefacts/right-angle-simplices-notes.md's
#   Kozlov-vector extremal-matrix section. Found and confirmed a real bug:
#   the naive vector-sum h1 + shift^d(h2) of two rank-1 Hilbert functions
#   (dropping the trivial degree-0 coordinate throughout) is NOT the true
#   Hilbert function of F/M for F = Eg_1 (+) Eg_2, deg g_2 = d -- it is
#   missing exactly "+1" at ambient degree d (the surviving generator g_2's
#   own degree-0 contribution, H_{E/I_2}(0)=1, which the naive shift wrongly
#   zeroes out). Confirmed both numerically (this script) and by hand via a
#   direct monomial-basis count for n=2, d=1 (see
#   ../../transcripts/session-images-2026-08-06-1156.org's TEXIMG-9
#   correction). So conv(achievable rank-2 Hilbert functions) = R + e_d,
#   not R itself as TEXIMG-9 originally (wrongly) claimed.

def kk_cascade(m, i):
    terms = []
    remaining = m
    level = i
    a_bound = None
    while remaining > 0 and level >= 1:
        a = level - 1
        while binomial(a + 1, level) <= remaining and (a_bound is None or a + 1 < a_bound):
            a += 1
        terms.append((a, level))
        remaining -= binomial(a, level)
        a_bound = a
        level -= 1
    assert remaining == 0, (m, i, terms, remaining)
    return terms

def kk_shadow_bound(m, i):
    if m == 0:
        return 0
    return sum(binomial(a, level + 1) for (a, level) in kk_cascade(m, i - 1))

def enumerate_f_vectors(n):
    results = []
    def rec(prefix):
        i = len(prefix) + 1
        if i > n:
            results.append(tuple(prefix))
            return
        hi = n if i == 1 else kk_shadow_bound(prefix[-1], i)
        for f_i in range(hi + 1):
            rec(prefix + [f_i])
    rec([])
    return results

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

def unit(k, N):
    e = [0] * N
    e[k - 1] = 1
    return e

def check(n):
    a = kozlov_vector(n)
    F1_all = [f for f in enumerate_f_vectors(n) if f[0] == n]
    F1 = right_angle_vertices(a)  # vertices of conv(F1_all) = kozlov_simplex(n)
    assert set(map(tuple, F1)) <= set(F1_all)

    results = []
    for d in range(1, n):
        N = n + d
        Apad = Polyhedron(vertices=[pad(v, N) for v in F1])
        Ashift = Polyhedron(vertices=[shift_naive(v, d, N) for v in F1])
        C = Apad + Ashift  # = R, exactly as built throughout right_angle_simplex.py

        S_naive_pts = [[pad(h1, N)[k] + shift_naive(h2, d, N)[k] for k in range(N)]
                       for h1 in F1 for h2 in F1]
        S_naive = Polyhedron(vertices=S_naive_pts)

        ed = unit(d, N)
        S_true = Polyhedron(vertices=[[p[k] + ed[k] for k in range(N)] for p in S_naive_pts])
        C_plus_ed = C + Polyhedron(vertices=[ed])

        results.append(dict(
            d=d, n_vertices=C.n_vertices(),
            C_eq_Snaive=(C == S_naive), C_eq_Strue=(C == S_true),
            Cplused_eq_Strue=(C_plus_ed == S_true),
        ))
    return results

for row in check(6):
    print(row)
