# kozlov_facets_attempt_explore.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Exploration for the attempt on conj-kozlov-facets:
#               for each facet normal u of R(a;d), print the per-summand argmax
#               sets A_p = {j : u.v_p(j) maximal} and the dimension of the face
#               u exposes on each summand.  The goal is to read off the
#               combinatorial pattern of facet-normal cones before proving it.
#               See working-notes/conj-kozlov-facets-attempt.org.
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools

def kozlov(n): return [binomial(n,j) for j in range(1,n+1)]

def verts(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k))
            for k in range(1,len(a)+1)]

def explore(a,ds,label):
    n=len(a); N=n+max(ds); r=len(ds); s=len(set(ds))
    Vs=[verts(a,d,N) for d in ds]
    pts=[sum(t[1:],t[0]) for t in itertools.product(*Vs)]
    R=Polyhedron(vertices=pts,base_ring=QQ)
    ineqs=[hh for hh in R.Hrepresentation() if hh.is_inequality()]
    print("== %s  a=%s d=%s N=%d : dim=%d verts=%d facets=%d  s*n=%d"%(
        label,a,ds,N,R.dim(),R.n_vertices(),len(ineqs),s*n))
    for hh in ineqs:
        u=-vector(QQ,hh.A())
        g=gcd([x for x in u if x!=0]); u=u/g
        row=[]
        for p in range(r):
            vals=[u.dot_product(v) for v in Vs[p]]
            M=max(vals); A=[j+1 for j,x in enumerate(vals) if x==M]
            # dim of exposed face on summand p: |A|-1 (simplex)
            row.append("A%d=%s"%(p+1,A))
        print("   u=%-30s h=%-6s %s"%(tuple(u),-hh.b() if False else max(u.dot_product(q) for q in pts)," ".join(row)))
    print()

for (n,ds) in [(4,[0,1]),(4,[0,2]),(4,[0,3]),(5,[0,1]),(5,[0,2]),(5,[0,3]),(5,[0,4]),
               (4,[0,1,2]),(4,[0,2,3]),(5,[0,1,2]),(4,[0,1,2,3])]:
    explore(kozlov(n),ds,"KOZLOV")

for (n,ds) in [(4,[0,1]),(4,[0,1,2]),(5,[0,1])]:
    explore([1]*n,ds,"ALLONES")
