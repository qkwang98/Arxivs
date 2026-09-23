# logconvex_breaks_consecutive_reduction.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Independent confirmation of the subagent's log-convex
#               witness, which refutes the CONSECUTIVE form of the pairwise
#               reduction for a general leg vector.
#
# a = (1,2,6,24) = (1!,2!,3!,4!) has slopes sigma(i) = 2, 3, 4 -- strictly
# INCREASING, so a is log-convex, the opposite of Kozlov.  With n = 4 and
# d = (0,1,2), the tuple j = (4,1,1) passes BOTH consecutive pairwise tests, fails
# the non-consecutive pair (1,3), and is NOT extremal.
#
# Aggregate: 30 extremal tuples; the consecutive prediction gives 32 (two too
# many); the all-pairs prediction gives exactly 30.  So the ALL-PAIRS reduction
# survives here and the CONSECUTIVE sharpening does not.
#
# Consequence for the project: the "constraint network is a path" finding of
# working-notes/pairwise-reduction-proof-strategies.org is leg-vector dependent,
# not a general fact about right-angle simplices.  It holds under log-concavity,
# which Kozlov satisfies strictly and all-ones weakly.  The manuscript's Remark
# obs-pairwise is unaffected, being scoped to those two leg vectors.

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def ext(vl,N):
    idx=list(itertools.product(*[range(len(v)) for v in vl]))
    pts={t:sum((vl[k][t[k]] for k in range(len(vl))),vector(QQ,[0]*N)) for t in idx}
    P=Polyhedron(vertices=list(pts.values()),base_ring=QQ)
    V=set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}
a=[1,2,6,24]; n=4; ds=[0,1,2]; N=n+max(ds)
print("a =",a,"  slopes sigma(i)=a(i+1)/a(i):",[QQ(a[i+1])/a[i] for i in range(n-1)],"-> log-CONVEX")
V=[verts(a,d,N) for d in ds]
T=ext(V,N)
j=(3,0,0)   # 1-based (4,1,1)
pr={(p,q):ext([V[p],V[q]],N) for p in range(3) for q in range(p+1,3)}
print("\nwitness j = (4,1,1) one-based = %s zero-based"%(j,))
print("  extremal?                       ", j in T)
print("  consecutive pair (1,2) ok?      ", (j[0],j[1]) in pr[(0,1)])
print("  consecutive pair (2,3) ok?      ", (j[1],j[2]) in pr[(1,2)])
print("  NON-consecutive pair (1,3) ok?  ", (j[0],j[2]) in pr[(0,2)])
cons={t for t in itertools.product(range(n),repeat=3)
      if (t[0],t[1]) in pr[(0,1)] and (t[1],t[2]) in pr[(1,2)]}
allp={t for t in itertools.product(range(n),repeat=3)
      if all((t[p],t[q]) in pr[(p,q)] for p in range(3) for q in range(p+1,3))}
print("\n  |extremal|=%d  |consecutive-predicted|=%d  |all-pairs-predicted|=%d"%(len(T),len(cons),len(allp)))
print("  consecutive reduction holds? %s      all-pairs reduction holds? %s"%(cons==T, allp==T))
