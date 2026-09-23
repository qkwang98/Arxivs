# kozlov_facets_verification.sage
#
# Changelog (reverse chronological):
#   2026-09-05  Created.  Verifies the facet (H-)description of the Kozlov simplex
#               Kozlov(n) that article draft 3 states as a corollary of Kozlov's
#               theorem -- Jan's handwritten plan (article/first-article.pdf, p. 2)
#               asks for "facets as well, can't be hard!", and this is the check
#               behind that claim.  Also re-verifies the worked rank-r example
#               (n=3, d=(0,1)) used in the article and in
#               working-notes/kozlov-simplex-and-kozlov-polytope.org.
#
# Run from this directory:   sage kozlov_facets_verification.sage

def kozlov_vertices(n):
    """f-vectors of the complete k-skeleta on [n], k = 1..n (cardinality convention,
    degree-0 entry dropped): v_k = (C(n,1), ..., C(n,k), 0, ..., 0)."""
    return [tuple([binomial(n, j) for j in range(1, k + 1)] + [0] * (n - k))
            for k in range(1, n + 1)]


def kozlov_from_vertices(n):
    return Polyhedron(vertices=kozlov_vertices(n), base_ring=QQ)


def kozlov_from_facets(n):
    """The claimed H-representation:
           x_1 = n,   x_1/C(n,1) >= x_2/C(n,2) >= ... >= x_n/C(n,n) >= 0.
    Sage wants inequalities as b + a.x >= 0."""
    eqns = [[-n] + [1] + [0] * (n - 1)]           # x_1 - n = 0
    ieqs = []
    for j in range(1, n):                          # x_j/C(n,j) - x_{j+1}/C(n,j+1) >= 0
        row = [0] * (n + 1)
        row[j] = QQ(1) / binomial(n, j)
        row[j + 1] = -QQ(1) / binomial(n, j + 1)
        ieqs.append(row)
    row = [0] * (n + 1)                            # x_n >= 0
    row[n] = 1
    ieqs.append(row)
    return Polyhedron(ieqs=ieqs, eqns=eqns, base_ring=QQ)


print("=== Kozlov(n): V-description vs. claimed H-description ===")
for n in range(1, 10):
    P = kozlov_from_vertices(n)
    Q = kozlov_from_facets(n)
    print("n=%2d  equal=%-5s  dim=%d  #vertices=%d  #facets=%d  simplex=%s"
          % (n, P == Q, P.dimension(), P.n_vertices(), P.n_facets(),
             P.n_vertices() == P.dimension() + 1))

print()
print("=== the n=1 degenerate case, stated separately in the article ===")
print("Kozlov(1) =", kozlov_from_vertices(1).vertices_list())

print()
print("=== worked rank-r example: n=3, d=(0,1), degree-0-inclusive coordinates ===")
# S_n lives in R^{n+1} with leading coordinate 1; shift^d prepends d zeros.
def kozlov_deg0(n, d, N):
    """shift^d(Kozlov(n)) padded into R^{N+1}."""
    verts = []
    for v in kozlov_vertices(n):
        w = [0] * (N + 1)
        w[d] = 1                                   # the degree-0 entry, f_0 = 1
        for j, c in enumerate(v):
            w[d + 1 + j] = c
        verts.append(w)
    return Polyhedron(vertices=verts, base_ring=QQ)

n, ds = 3, [0, 1]
N = n + max(ds)
R = kozlov_deg0(n, ds[0], N)
for d in ds[1:]:
    R = R + kozlov_deg0(n, d, N)
print("R = Kozlov(3) + shift^1(Kozlov(3)) in R^5")
print("  dim      =", R.dimension())
print("  vertices =", sorted(R.vertices_list()))

print()
print("=== the same example in the degree-0-dropped coordinates of angle(a) ===")
def angle(a, d, N):
    verts = []
    for k in range(1, len(a) + 1):
        w = [0] * N
        for j in range(k):
            w[d + j] = a[j]
        verts.append(w)
    return Polyhedron(vertices=verts, base_ring=QQ)

a = [binomial(3, j) for j in range(1, 4)]
N = 3 + 1
R2 = angle(a, 0, N) + angle(a, 1, N)
print("  a        =", a)
print("  dim      =", R2.dimension())
print("  vertices =", sorted(R2.vertices_list()))

print()
print("=== dim Koz(n;d) = |union_i {d_i+2,...,d_i+n}| ===")
bad = 0
count = 0
for n in range(2, 6):
    for ds in [[0, 0], [0, 1], [0, 2], [0, n - 1], [0, n],
               [0, 0, 0], [0, 1, 1], [0, 1, 2], [0, 2, 4], [0, 1, 2, 3]]:
        Nd = n + max(ds)
        P = kozlov_deg0(n, ds[0], Nd)
        for d in ds[1:]:
            P = P + kozlov_deg0(n, d, Nd)
        idx = set()
        for d in ds:
            idx |= set(range(d + 2, d + n + 1))
        count += 1
        if P.dimension() != len(idx):
            bad += 1
            print("  MISMATCH n=%d d=%s: %d vs %d" % (n, ds, P.dimension(), len(idx)))
print("  configurations checked: %d (r = 2,3,4; n = 2..5).  disagreements: %d" % (count, bad))
