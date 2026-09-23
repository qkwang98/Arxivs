# mu_candidates_do_not_suffice.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Refutes the claim, made in an earlier draft of section
#               8.6, that the facet normals of R are the summands' own facet
#               normals (the mu-chain of cor-facets), at most r*n of them.
#
# Result: the mu-candidates do NOT cut out R, in every configuration tested, and
# they fail already at n = 3 -- not only for n >= 4.  For n = 3, d = (0,1): R has
# six facets; only FOUR of the six mu-candidates define facets, the other two
# cutting faces of dimension one; and two facets of R are of a different shape
# entirely (lower bounds x(d_p + 1) >= a_1 and a matching upper bound past the end
# of the previous window).
#
# WHY the shortcut fails.  Facets correspond to RAYS of the normal fan, and rays of
# a common refinement are the union of the summands' rays only when the summands
# are FULL-DIMENSIONAL.  Ours are not, and -- the operative point -- they have
# DIFFERENT lineality spaces, so intersecting their cones creates rays belonging to
# no summand's fan.  prop-faceadd still gives the weaker necessary condition that a
# facet normal lies on a wall of some summand's fan, but walls correspond to edges,
# so the a priori bound is r*binom(n,2), not r*n.
#
# Note the recurring trap: comparing normals directly is unreliable here, since
# e.g. (-1,1,0,0) and (0,1,0,0) differ by lineality and are the same facet. Use the
# dimension of the exposed face, as this script does.

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def R_of(a,ds,N):
    return Polyhedron(vertices=[sum((verts(a,ds[i],N)[t[i]] for i in range(len(ds))),vector(QQ,[0]*N))
                      for t in itertools.product(range(len(a)),repeat=len(ds))],base_ring=QQ)
def mu_candidates(a,d,N):
    """cor-facets inequalities for the summand at shift d, as OUTWARD normals in R^N."""
    n=len(a); out=[]
    for j in range(1,n):                       # x(d+j)/a_j >= x(d+j+1)/a_{j+1}
        u=vector(QQ,[0]*N); u[d+j-1]=-QQ(1)/a[j-1]; u[d+j]=QQ(1)/a[j]; out.append(u)
    u=vector(QQ,[0]*N); u[d+n-1]=-1; out.append(u)      # x(d+n) >= 0
    return out
print("Is R cut out by the mu-candidates alone?  (draft 5 asserts the candidates are these)")
print("   n  d          facets(R)  #mu-cands   Q == R ?   #mu-cands that are NOT facets of R")
for n in (3,4,5):
  a=[binomial(n,j) for j in range(1,n+1)]
  for ds in ([0,1],[0,2],[0,1,2]):
    if n==5 and len(ds)>2: continue
    N=n+max(ds); R=R_of(a,ds,N)
    C=[u for d in ds for u in mu_candidates(a,d,N)]
    eqs=[[h.b()]+list(h.A()) for h in R.Hrepresentation() if h.is_equation()]
    ieqs=[[max(u.dot_product(v.vector()) for v in R.vertices())*-1]+list(-u) for u in C]
    Q=Polyhedron(ieqs=ieqs,eqns=eqs,base_ring=QQ)
    # which candidates are actually facets of R?
    nonfacet=0
    for u in C:
        hv=max(u.dot_product(v.vector()) for v in R.vertices())
        F=[v.vector() for v in R.vertices() if u.dot_product(v.vector())==hv]
        if Polyhedron(vertices=F,base_ring=QQ).dim()!=R.dim()-1: nonfacet+=1
    nf=len([h for h in R.Hrepresentation() if h.is_inequality()])
    print("   %d  %-10s %8d %10d   %-8s %d"%(n,ds,nf,len(C),Q==R,nonfacet))
