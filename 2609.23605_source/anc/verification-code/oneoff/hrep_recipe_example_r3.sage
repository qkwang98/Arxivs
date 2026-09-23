# hrep_recipe_example_r3.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Worked r=3 example for the H-description recipe.
#
# Companion: code/oneoff/hrep_recipe_example_r3.jl runs the SAME example in
# OSCAR/Polymake, a completely independent polyhedral backend from Sage's
# cddlib/PPL.  Both agree on dim, vertex count, facet count, every facet normal
# and every offset.  See working-notes/hrepresentation-normal-fans-and-pruning.org.
#
# Example: n = 3, Kozlov leg vector a = (3,3,1), shifts d = (0,1,2), so N = 5.
# Result: dim 4, 16 vertices, 9 facets -- exactly r*n = 9, nothing pruned.
# Support-function additivity h_R(u) = sum_i h_i(u) holds on every facet, as it
# must; the content is only WHICH u are facet normals, and every one of them lies
# on a wall of at least two of the three summands.

import itertools
n=3; a=[binomial(n,j) for j in range(1,n+1)]; ds=[0,1,2]; N=n+max(ds); r=len(ds)
def verts(d): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,n+1)]
S=[Polyhedron(vertices=verts(d),base_ring=QQ) for d in ds]
pts=[sum((verts(ds[i])[t[i]] for i in range(r)),vector(QQ,[0]*N)) for t in itertools.product(range(n),repeat=r)]
R=Polyhedron(vertices=pts,base_ring=QQ)
print("SAGE (cddlib/PPL)   a=%s  d=%s  N=%d"%(a,ds,N))
print("  dim=%d  vertices=%d  facets=%d   r*n=%d"%(R.dim(),len(R.vertices()),
      len([h for h in R.Hrepresentation() if h.is_inequality()]),r*n))
def h(P,u): return max(u.dot_product(v.vector()) for v in P.vertices())
print("\n  facet normals u (outward), and the additivity check h_R(u) = sum_i h_i(u):")
print("  %-22s %6s %6s %6s %6s  %s"%("u","h_R","h_1","h_2","h_3","walls"))
ok=True
for hh in R.Hrepresentation():
    if not hh.is_inequality(): continue
    u=-vector(QQ,hh.A()); g=gcd([x for x in u if x!=0]); u=u/g
    hs=[h(P,u) for P in S]; add = (h(R,u)==sum(hs)); ok&=add
    walls=[i+1 for i,P in enumerate(S)
           if Polyhedron(vertices=[v.vector() for v in P.vertices()
                                   if u.dot_product(v.vector())==h(P,u)],base_ring=QQ).dim()>=1]
    print("  %-22s %6s %6s %6s %6s  %s"%(tuple(u),h(R,u),hs[0],hs[1],hs[2],walls))
print("\n  support-function additivity held for every facet: %s"%ok)
