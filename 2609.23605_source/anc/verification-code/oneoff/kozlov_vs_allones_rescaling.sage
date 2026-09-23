# kozlov_vs_allones_rescaling.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Tests whether the diagonal rescaling that identifies the
#               Kozlov simplex with the all-ones right-angle simplex at rank 1
#               survives Minkowski summation at rank >= 2.  It does not.
#
# Rank 1: D = diag(binom(n,1),...,binom(n,n)) carries angle(1,...,1) to angle(a)
# vertex by vertex, so the two are linearly isomorphic and the induced map on
# lattices sends f to (f_j / binom(n,j)) -- the mu-coordinates of Lemma lem-mu.
#
# Rank >= 2: no single linear map can do this, because summand i would need
# coordinate m divided by binom(n, m - d_i), a factor depending on i, while
# overlapping windows share coordinates.  Confirmed here by f-vector comparison.
#
# Result: the two vertex counts are n^2 - m(m-1) (all-ones) and
# n^2 - (m-1)(m+2)/2 (Kozlov), m = n-d, differing by exactly (m-1)(m-2)/2.
# So they agree precisely when m <= 2 and diverge from m = 3 onward -- the same
# gap threshold that Proposition prop-gapK turns on.

def verts(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def P(a,ds,N):
    import itertools
    pts=[sum((verts(a,d,N)[t[i]] for i,d in enumerate(ds)),vector(QQ,[0]*N))
         for t in itertools.product(range(len(a)),repeat=len(ds))]
    return Polyhedron(vertices=pts,base_ring=QQ)
print("rank 1: is angle(Kozlov) = D(angle(all-ones))?")
for n in (3,4,5):
    a=[binomial(n,j) for j in range(1,n+1)]
    K=P(a,[0],n); U=P([1]*n,[0],n)
    D=matrix(QQ,n,n,lambda i,j: a[i] if i==j else 0)
    print("  n=%d  D(unit)==Kozlov: %s" % (n, Polyhedron(vertices=[D*v.vector() for v in U.vertices()])==K))
print("\nrank 2: vertex counts, all-ones vs Kozlov  (formula check too)")
print("   n  d   #V(ones)  pred   #V(Koz)  pred   same combinatorial type?")
for n in (4,5,6):
  for d in range(1,n):
    m=n-d
    U=P([1]*n,[0,d],n+d); K=P([binomial(n,j) for j in range(1,n+1)],[0,d],n+d)
    pu=n^2-(n-d)*(n-d-1); pk=n^2-(m-1)*(m+2)/2
    fu=U.f_vector(); fk=K.f_vector()
    print("  %2d %2d %8d %6d %8d %6d   %s" % (n,d,len(U.vertices()),pu,len(K.vertices()),pk,
          "yes" if fu==fk else "NO  (f-vectors differ)"))
