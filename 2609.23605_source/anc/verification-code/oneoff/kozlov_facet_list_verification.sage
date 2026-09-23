# kozlov_facet_list_verification.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Verifies the EXPLICIT facet-list hypothesis for
#               conj-kozlov-facets found during the proof attempt (see
#               working-notes/conj-kozlov-facets-attempt.org).  For the Kozlov
#               vector a(i)=C(n,i) and strictly increasing shifts d(1)=0<...<d(r)
#               with all gaps <= n-1 (the reduced case: ties, common shifts and
#               gaps >= n are handled by proved reductions), the claim is that
#               the facet normals of R, modulo the lineality e(1) and positive
#               scaling, are EXACTLY the r*n vectors:
#                 item 1:  e(2)                                  [window 1, j=1]
#                 item 2:  e(d(p)+j+1)/a(j+1) - e(d(p)+j)/a(j),  p=1..r, j=2..n-1
#                 item 3: -e(N)                                  [window r, j=n]
#                 item 4: -e(d(p)+1),          p=2..r            [lower extras]
#                 item 5: +e(d(p-1)+n+1),      p=2..r            [upper extras]
#               The script compares this predicted set against the actual
#               H-representation (primitive integer normals, outward), for a
#               grid of (n, d) configurations, and reports any mismatch.
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools

def kozlov(n): return [binomial(n,j) for j in range(1,n+1)]

def verts(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k))
            for k in range(1,len(a)+1)]

def primitive(u):
    den=lcm([x.denominator() for x in u if x!=0])
    u=vector(ZZ,u*den)
    g=gcd([x for x in u if x!=0])
    return tuple(u/g)

def predicted(a,ds):
    n=len(a); r=len(ds); N=n+ds[-1]
    def e(c):
        v=[0]*N; v[c-1]=1; return vector(QQ,v)
    L=[e(2)]                                             # item 1
    for p in range(r):                                   # item 2
        for j in range(2,n):
            L.append(e(ds[p]+j+1)/a[j] - e(ds[p]+j)/a[j-1])
    L.append(-e(N))                                      # item 3
    for p in range(1,r):
        L.append(-e(ds[p]+1))                            # item 4
        L.append(e(ds[p-1]+n+1))                         # item 5
    return L

def actual_normals(a,ds):
    n=len(a); N=n+ds[-1]
    Vs=[verts(a,d,N) for d in ds]
    pts=[sum(t[1:],t[0]) for t in itertools.product(*Vs)]
    R=Polyhedron(vertices=pts,base_ring=QQ)
    return R, set(primitive(-vector(QQ,hh.A()))
                  for hh in R.Hrepresentation() if hh.is_inequality())

def check(a,ds,label):
    n=len(a); r=len(ds)
    P=[primitive(u) for u in predicted(a,ds)]
    Pset=set(P)
    assert len(Pset)==len(P)==r*n, "predicted list not distinct! %s %s"%(a,ds)
    R,A=actual_normals(a,ds)
    ok = (Pset==A)
    print("%s n=%d d=%-14s dim=%d facets=%d rn=%d  LIST MATCH: %s"%(
        label,n,ds,R.dim(),len(A),r*n,ok))
    if not ok:
        print("   predicted-only:",sorted(Pset-A))
        print("   actual-only:   ",sorted(A-Pset))
    return ok

allok=True; count=0
for n in (2,3,4,5,6):
    a=kozlov(n)
    gaps_list=[]
    for r1 in (1,2,3):                       # r-1 gaps
        if n==2 and r1>2: continue
        if n>=6 and r1>2: continue
        if n>=5 and r1>3: continue
        for gs in itertools.product(range(1,n),repeat=r1):
            ds=[0]
            for g in gs: ds.append(ds[-1]+g)
            if n+ds[-1]>16: continue
            if n>=5 and r1>=3 and max(gs)>2: continue   # keep runtime sane
            gaps_list.append(ds)
    for ds in gaps_list:
        count+=1
        allok = check(a,ds,"KOZLOV") and allok
print()
print("checked %d configurations; all matched: %s"%(count,allok))
