# kozlov_facets_greedy_peel_test.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Tests the inductive decomposition step proposed for the
#               completeness half of conj-kozlov-facets (see
#               working-notes/conj-kozlov-facets-attempt.org): given x in
#               R = P(1)+...+P(r), peel window 1 by
#                   y(c) = x(c)                     for c <= d(2)
#                   y(c) = max(0, x(c) - M(c))      for d(2)+1 <= c <= n
#                   y(c) = 0                        for c > n
#               where M(c) = sum over q>=2 of a(c-d(q)) when 1<=c-d(q)<=n
#               (the max of coordinate c over the later windows' sum), and test
#               whether y in P(1) and x - y in P(2)+...+P(r), for vertices and
#               random rational points of R.  At rank 2 this step is PROVED;
#               at rank >= 3 the chain algebra was unclear, hence this test.
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools

def kozlov(n): return [binomial(n,j) for j in range(1,n+1)]

def verts(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k))
            for k in range(1,len(a)+1)]

set_random_seed(20260906)

def test(a,ds,npts=60):
    n=len(a); r=len(ds); N=n+ds[-1]
    Vs=[verts(a,d,N) for d in ds]
    pts=[sum(t[1:],t[0]) for t in itertools.product(*Vs)]
    R=Polyhedron(vertices=pts,base_ring=QQ)
    P1=Polyhedron(vertices=Vs[0],base_ring=QQ)
    Rrest=Polyhedron(vertices=[sum(t[1:],t[0]) for t in itertools.product(*Vs[1:])],
                     base_ring=QQ)
    M=[sum(a[c-d-1] for d in ds[1:] if 1<=c-d<=n) for c in range(1,N+1)]
    samples=[v.vector() for v in R.vertices()]
    Vlist=[v.vector() for v in R.vertices()]
    for _ in range(npts):
        k=ZZ.random_element(2,min(6,len(Vlist))+1)
        ws=[QQ(ZZ.random_element(1,7)) for _ in range(k)]; s=sum(ws)
        idx=[ZZ.random_element(0,len(Vlist)) for _ in range(k)]
        samples.append(sum((ws[i]/s)*Vlist[idx[i]] for i in range(k)))
    bad=0
    for x in samples:
        y=vector(QQ,[x[c-1] if c<=ds[1] else (max(0,x[c-1]-M[c-1]) if c<=n else 0)
                     for c in range(1,N+1)])
        if not (y in P1 and (x-y) in Rrest):
            bad+=1
            if bad<=3:
                print("   FAIL n=%d d=%s x=%s y=%s  yinP1=%s restin=%s"%(
                    n,ds,x,y,y in P1,(x-y) in Rrest))
    print("n=%d d=%-12s samples=%d failures=%d"%(n,ds,len(samples),bad))
    return bad==0

allok=True
for (n,ds) in [(3,[0,1,2]),(4,[0,1,2]),(4,[0,2,3]),(4,[0,1,3]),(4,[0,2,4]),
               (4,[0,3,4]),(5,[0,1,2]),(5,[0,2,4]),(5,[0,1,4]),(4,[0,1,2,3]),
               (5,[0,2,3]),(3,[0,2,4]),(4,[0,3,6]),(5,[0,4,8])]:
    allok=test(kozlov(n),ds) and allok
print("ALL OK:",allok)
