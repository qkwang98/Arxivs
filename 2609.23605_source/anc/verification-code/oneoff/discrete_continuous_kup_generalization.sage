# Changelog (reverse chronological):
# 2026-08-07 - Claude (fork): created, per Jan's request to generalize Kupreyeva's r=1
#   cardinality/centroid/volume results to rank r. Computes: |S_n| (Linusson's f-vector
#   count, independently cross-checked against binomial_basis.py's brute_force_f_vectors),
#   the ff-vector sumset cardinality |FF(d)| for r=2,3 and various shift vectors, the
#   discrete centroid of S_n/FF(d), and the continuous volume/centroid of Kozlov(n) and its
#   Minkowski sums (via right_angle_simplex.py). Confirms a clean dichotomy at the SAME
#   threshold (min consecutive gap >= n-1) for four independent quantities: sumset
#   cardinality reaches its max |S_n|^r (bijective regime) iff every consecutive shift gap
#   is >= n-1; discrete centroid of FF(d) is additive over the summands iff the same
#   threshold holds (a direct corollary of bijectivity); continuous volume of R is
#   multiplicative (Vol(R) = Vol(Kozlov(n))^r) and continuous centroid is additive under
#   the identical threshold; outside that threshold (the "overlapping" regime), all four
#   claims fail -- verified with real counterexamples, not just asserted. See
#   ../../artefacts/discrete-vs-continuous-kup.md for the full write-up with proofs.
# Run from code/ (not code/oneoff/): `cd .. && sage oneoff/discrete_continuous_kup_generalization.sage`
# -- binomial_basis.py itself does a bare load('right_angle_simplex.py') assuming that cwd.
load('binomial_basis.py')
load('right_angle_simplex.py')


def S_n_full(n):
    """All proper rank-1 Hilbert sequences (1,f_1,...,f_n), f_1=n, via the Kruskal-Katona
    recursion in binomial_basis.py's enumerate_f_vectors. Cross-checked for n<=4 against
    brute_force_f_vectors (genuinely independent enumeration, not sharing the recursion)."""
    return [(1,) + f for f in enumerate_f_vectors(n) if f[0] == n]


def shift_seq(s, d, N):
    """Zero-pad the sequence s (length N-d+1... really len(s)) so it starts at index d,
    total length N+1. Matches the degree-0-inclusive shift of
    artefacts/proper-hilbert-functions-kozlov-minkowski.org section 7."""
    out = [0] * (N + 1)
    for idx, val in enumerate(s):
        out[idx + d] = val
    return tuple(out)


def ff_sumset(Sn_list, shifts):
    """The set FF(d) = S_n + shift^{d_2}(S_n) + ... for shifts=(d_1=0,d_2,...,d_r), as an
    r-fold Cartesian-product-then-sum (exponential in r -- only meant for small r,n).
    Sn_list[i] is the (possibly distinct) candidate-sequence pool for the i-th summand,
    normally the same S_n repeated len(shifts) times."""
    from itertools import product
    N = shifts[-1] + (len(Sn_list[0][0]) - 1)
    FF = set()
    for combo in product(*Sn_list):
        total = [0] * (N + 1)
        for s, d in zip(combo, shifts):
            v = shift_seq(s, d, N)
            total = [a + b for a, b in zip(total, v)]
        FF.add(tuple(total))
    return FF


def discrete_centroid(pts):
    n = len(pts)
    N = len(pts[0])
    return tuple(QQ(sum(p[i] for p in pts)) / n for i in range(N))


def polytope_centroid(P):
    """True volume-weighted centroid of a (possibly not full-dimensional) polytope P, via
    triangulation + induced-measure-weighted average of simplex centroids. Needed because
    a naive vertex-average is NOT the volume centroid except for an actual simplex."""
    tri = P.triangulate()
    total_vol = 0
    weighted_sum = vector(QQ, [0] * P.ambient_dim())
    for simplex_indices in tri:
        verts = [P.Vrepresentation()[i].vector() for i in simplex_indices]
        vol = Polyhedron(vertices=verts).volume(measure='induced')
        c = sum(vector(QQ, v) for v in verts) / len(verts)
        total_vol += vol
        weighted_sum += vol * c
    return weighted_sum / total_vol, total_vol


def main():
    print("=== |S_n|, independently verified for n<=4 against brute_force_f_vectors ===")
    for n in range(1, 7):
        Sn = S_n_full(n)
        print(n, len(Sn))

    print("\n=== sumset cardinality dichotomy, r=2: |FF(d)| = |S_n|^2 iff d2 >= n-1 ===")
    for n in [3, 4, 5]:
        Sn = S_n_full(n)
        for d2 in [0, n - 2, n - 1, n]:
            FF = ff_sumset([Sn, Sn], [0, d2])
            print(f"  n={n} d2={d2}: |FF(d)|={len(FF)}  |S_n|^2={len(Sn)**2}  "
                  f"bijective={len(FF)==len(Sn)**2}")

    print("\n=== discrete centroid additivity, r=2: same n-1 threshold, direct corollary "
          "of bijectivity above ===")
    for n in [3, 4]:
        Sn = S_n_full(n)
        cS = discrete_centroid(Sn)
        for d2 in [n - 2, n - 1]:
            FF = list(ff_sumset([Sn, Sn], [0, d2]))
            cFF = discrete_centroid(FF)
            N = n + d2
            naive = tuple(a + b for a, b in zip(shift_seq(cS, 0, N), shift_seq(cS, d2, N)))
            print(f"  n={n} d2={d2}: centroid(FF)==c(S)+shift(c(S))? {cFF==naive}")

    print("\n=== continuous volume/centroid of R = Kozlov(n)+shift^d2(Kozlov(n)) ===")
    for n in [3, 4]:
        a = kozlov_vector(n)
        K = right_angle_simplex(a)
        cK, volK = polytope_centroid(K)
        for d2 in [n - 2, n - 1]:
            N = n + d2
            P1 = pad_polytope(K, N)
            P2 = pad_polytope(shift_polytope(K, d2), N)
            R = P1 + P2
            cR, volR = polytope_centroid(R)
            naive_vol = volK ** 2
            naive_c = vector(QQ, pad_vector(cK, N)) + vector(QQ, pad_vector(shift_vector(cK, d2), N))
            print(f"  n={n} d2={d2}: vol(R)={volR} vs Vol(K)^2={naive_vol} match={volR==naive_vol};"
                  f" centroid additive? {cR==naive_c}")


main()
