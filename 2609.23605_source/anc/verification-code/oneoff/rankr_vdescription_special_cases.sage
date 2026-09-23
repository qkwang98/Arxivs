# rankr_vdescription_special_cases.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Verifies the three special cases of the rank-r
#               V-description proved in
#               working-notes/rank-r-vdescription-special-cases.org.
#
# A: shift vector takes at most TWO distinct values => the consecutive pairwise
#    reduction holds, for any r, any n, any positive leg vector.  Mechanism is
#    collapsing (equal shifts force equal vertex indices), not gluing.
#    Verified over 16 configurations: 0 mismatches, and the structural
#    prediction matches the extremal tensor exactly.
# B: all consecutive gaps >= n-1  =>  M is identically 1.  Because a summand
#    does not constrain its window's FIRST coordinate (every vertex has first
#    coordinate a_1, a constant offset in every partial sum), so it constrains
#    only [d(p)+2, d(p)+n], and those are pairwise disjoint at that gap.
#    Verified over 16 configurations, |support| = n^r every time.
# C: if j(p+1) + gap(p) > n for every p then M[j] = 1 unconditionally, by a
#    greedy left-to-right completion.  Verified: 230 qualifying tuples, 0
#    failures.
#
# None of these touches the hard case, which is three or more distinct shifts
# with small gaps.  See the note's closing section.

def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def ext(vl,N):
    idx=list(itertools.product(*[range(len(v)) for v in vl]))
    pts={t:sum((vl[k][t[k]] for k in range(len(vl))),vector(QQ,[0]*N)) for t in idx}
    P=Polyhedron(vertices=list(pts.values()),base_ring=QQ)
    V=set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}
def consec_pred(n,ds,V,N):
    r=len(ds); pr={(p,p+1):ext([V[p],V[p+1]],N) for p in range(r-1)}
    return {t for t in itertools.product(range(n),repeat=r)
            if all((t[p],t[p+1]) in pr[(p,p+1)] for p in range(r-1))}

print("THEOREM A: shift vector takes at most TWO distinct values => reduction holds")
print("  also predicts M[j]=1 iff j constant on each shift-group and the two groups' pair is ok")
bad=0
for aname in ("kozlov","ones"):
 for n in (3,4):
  a=[binomial(n,j) for j in range(1,n+1)] if aname=="kozlov" else [1]*n
  for ds in ([0,0,0],[0,0,2],[0,2,2],[0,0,1],[0,0,0,0],[0,0,2,2],[0,1,1,1],[0,0,0,3]):
    N=n+max(ds); V=[verts(a,d,N) for d in ds]; T=ext(V,N); C=consec_pred(n,ds,V,N)
    # structural prediction
    pair=ext([verts(a,min(ds),N),verts(a,max(ds),N)],N) if len(set(ds))==2 else None
    pred=set()
    for t in itertools.product(range(n),repeat=len(ds)):
        g={}; ok=True
        for p,d in enumerate(ds): g.setdefault(d,t[p]); ok &= (g[d]==t[p])
        if not ok: continue
        if len(set(ds))==1: pred.add(t)
        else:
            lo,hi=min(ds),max(ds)
            if (g[lo],g[hi]) in pair: pred.add(t)
    tag = "ok" if (T==C==pred) else "*** MISMATCH ***"
    bad += 0 if T==C==pred else 1
    print("  %-7s n=%d d=%-12s |T|=%4d |consec|=%4d |pred|=%4d  %s"%(aname,n,ds,len(T),len(C),len(pred),tag))
print("  Theorem A mismatches: %d\n"%bad)

print("THEOREM B: all consecutive gaps >= n-1  =>  M is identically 1")
bad=0
for aname in ("kozlov","ones"):
 for n in (3,4):
  a=[binomial(n,j) for j in range(1,n+1)] if aname=="kozlov" else [1]*n
  for ds in ([0,n-1,2*(n-1)],[0,n-1,2*n-1],[0,n,2*n],[0,n-1,2*(n-1),3*(n-1)]):
    N=n+max(ds); V=[verts(a,d,N) for d in ds]; T=ext(V,N)
    allones = (len(T)==n**len(ds))
    bad += 0 if allones else 1
    print("  %-7s n=%d d=%-16s |T|=%5d  n^r=%5d  all ones: %s"%(aname,n,ds,len(T),n**len(ds),allones))
print("  Theorem B mismatches: %d\n"%bad)

print("THEOREM C: if j(p+1) + gap_p > n for every p, then M[j]=1 unconditionally")
bad=0; tested=0
for aname in ("kozlov","ones"):
 for n in (3,4,5):
  a=[binomial(n,j) for j in range(1,n+1)] if aname=="kozlov" else [1]*n
  for ds in ([0,1,2],[0,2,3],[0,1,3],[0,2,4],[0,1,1],[0,1,2,3]):
    if len(ds)==4 and n==5: continue
    N=n+max(ds); V=[verts(a,d,N) for d in ds]; T=ext(V,N); r=len(ds)
    for t in itertools.product(range(n),repeat=r):   # t is 0-based; j = t+1
        if all((t[p+1]+1)+(ds[p+1]-ds[p])>n for p in range(r-1)):
            tested+=1
            if t not in T: bad+=1; print("   COUNTEREXAMPLE",aname,n,ds,t)
print("  Theorem C: %d tuples satisfied the hypothesis, %d failed to be vertices"%(tested,bad))
