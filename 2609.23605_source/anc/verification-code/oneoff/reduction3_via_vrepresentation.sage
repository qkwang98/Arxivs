# reduction3_via_vrepresentation.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created, at Jan's suggestion that reduction 3 of the
#               conj-kozlov-facets attempt can be argued on the V-side instead.
#
# It can, and the V-route gives a BETTER threshold: n-1 rather than n.
#
# Theorem B (working-notes/rank-r-vdescription-special-cases.org): if all gaps are
# >= n-1 then the effective coordinate sets [d(p)+2, d(p)+n] are pairwise disjoint,
# each summand's condition is satisfiable independently, and M is identically 1 --
# every one of the n^r vertex sums IS a vertex.  Then R is combinatorially the
# r-fold product of (n-1)-simplices, so its facet count is r*n by the product rule,
# which is the conjecture in that regime.
#
# Verified here: at gap >= n-1 the FULL f-vector of R equals that of the r-fold
# product, for n = 3,4,5 and r = 2,3 -- not merely the vertex and facet counts.
# At gap = n-2 it fails: strictly fewer than n^r vertices and a different f-vector.
#
# Worth noting for anyone using this as a reduction: the facet count is STILL r*n
# at gap = n-2 (6, 9, 8, 12, 10, 15 as predicted) even though R is no longer a
# product.  So the product argument disposes only of gap >= n-1, and the real
# content of the facet-count conjecture lies at SMALL gaps.

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def R_of(a,ds,N):
    return Polyhedron(vertices=[sum((verts(a,ds[i],N)[t[i]] for i in range(len(ds))),vector(QQ,[0]*N))
                      for t in itertools.product(range(len(a)),repeat=len(ds))],base_ring=QQ)
def nf(P): return len([h for h in P.Hrepresentation() if h.is_inequality()])
print("Reduction 3 via the V-side. Threshold n-1 (Thm B) rather than n?")
print("  A product of r copies of an (n-1)-simplex has n^r vertices, r*n facets,")
print("  and f-vector the product of the factors' f-vectors.")
print("\n  n  d-vector       gap  vertices  n^r   facets  r*n   f-vector == product?")
for n in (3,4,5):
  a=[binomial(n,j) for j in range(1,n+1)]
  for g in (n-2,n-1,n):
    for r in (2,3):
      ds=[g*i for i in range(r)]
      if g==0: continue
      N=n+max(ds); R=R_of(a,ds,N)
      S=Polyhedron(vertices=verts(a,0,n),base_ring=QQ)
      fv=list(R.f_vector()); 
      # f-vector of the r-fold product of S
      import functools
      P=S
      for _ in range(r-1): P=P.product(S)
      same = (list(P.f_vector())==fv)
      print("  %d  %-14s %3d %9d %5d %7d %5d   %s%s"%(n,ds,g,len(R.vertices()),n**r,nf(R),r*n,same,
            "   <-- gap = n-1" if g==n-1 else ("   <-- gap = n-2" if g==n-2 else "")))
