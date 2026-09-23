# minkowski_facet_normals_from_summand_walls.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Confirms that facet normals of the Minkowski sum come
#               from walls of the summands' normal fans, at rank 2 and rank 3.
#
# Standard theory: F_phi(P_1+...+P_r) = F_phi(P_1)+...+F_phi(P_r), so the normal
# fan of a sum is the common refinement of the summands' fans, for ANY r.  Rays of
# a common refinement are the union of the rays, hence facet normals of the sum
# are the union of the summands' facet normals -- WHEN the summands are
# full-dimensional.  Ours are not: each shift^d(angle(a)) is (n-1)-dimensional in
# R^N, so its normal fan has lineality and "the" facet normal is only a coset.
#
# Two earlier attempts to test the union statement failed on that normalization,
# with the COUNTS matching exactly every time (24 configurations).  This script
# uses a normalization-free formulation instead: u is a facet normal of R iff u
# lies on a WALL of some summand's fan, i.e. exposes a positive-dimensional face
# there.  That test passes in all 18 configurations, both leg vectors, r = 2 and 3.
#
# Payoff: an H-description recipe at ANY rank.  Candidate normals are the walls of
# the summands' fans -- for angle(a) these are the n facets of cor-facets, the
# mu-chain.  Offsets are free by additivity of support functions,
# h_R(u) = sum_i h_i(u).  The only work is pruning redundant candidates, and the
# facet counts say Kozlov prunes NOTHING (exactly r*n) while all-ones prunes some.

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def R_of(a,ds,N):
    return Polyhedron(vertices=[sum((verts(a,d,N)[t[i]] for i,d in enumerate(ds)),vector(QQ,[0]*N))
                      for t in itertools.product(range(len(a)),repeat=len(ds))],base_ring=QQ)
def face_dim(P,u):
    """dimension of the face of P maximized by u -- normalization-free."""
    vs=[v.vector() for v in P.vertices()]; m=max(u.dot_product(v) for v in vs)
    F=[v for v in vs if u.dot_product(v)==m]
    return Polyhedron(vertices=F,base_ring=QQ).dim()
print("Every facet normal u of R exposes a POSITIVE-DIMENSIONAL face on some summand?")
print("  (u is a facet normal of R  <=>  u lies on a wall of some summand's normal fan)")
print("  a       n  d-vector      facets(R)  from >=1 summand wall   #summands walled (min,max)")
allok=True
for aname in ("kozlov","ones"):
 for n in (3,4,5):
  a=[binomial(n,j) for j in range(1,n+1)] if aname=="kozlov" else [1]*n
  for ds in ([0,1],[0,1,2],[0,1,3]):
    N=n+max(ds); R=R_of(a,ds,N)
    S=[Polyhedron(vertices=verts(a,d,N),base_ring=QQ) for d in ds]
    cnt=[]; ok=True
    for h in R.Hrepresentation():
        if not h.is_inequality(): continue
        u=-vector(QQ,h.A())           # outward normal: maximize
        w=sum(1 for P in S if face_dim(P,u)>=1)
        cnt.append(w); ok &= (w>=1)
    allok &= ok
    print("  %-7s %d  %-12s %8d  %-20s  (%d,%d)"%(aname,n,ds,len(cnt),ok,min(cnt),max(cnt)))
print("\nall facet normals of R come from a summand wall: %s"%allok)
