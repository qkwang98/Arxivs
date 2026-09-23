# kozlov_hrep_theta_form_check.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. End-to-end check of the Theta-form H-description of the
#               Kozlov polytope R(a;d) found in the conj-kozlov-facets attempt
#               (working-notes/conj-kozlov-facets-attempt.org).  With
#               M^p(c) = sum over q>p of a(c-d(q)) when 1<=c-d(q)<=n  (the
#               "roof" of the windows after p) and
#               Theta^p(c) = (x(c) - M^p(c))/a(c-d(p)),
#               the claim is that R equals the set of x in R^N with
#                 (E)   x(1) = a(1)
#                 (I1)  Theta^1 non-increasing at links j=1..n-1
#                 (Ip)  Theta^p non-increasing at links j=2..n-1   (p=2..r)
#                 (Cp)  x(d(p)+1) >= a(1)                          (p=2..r)
#                 (Dp)  x(d(p-1)+n+1) <= M^{p-1}(d(p-1)+n+1)       (p=2..r)
#                 (F)   x(N) >= 0.
#               This system carries the offsets IMPLICITLY, so equality of
#               polyhedra here verifies both the facet-normal list and every
#               offset, plus the telescoping algebra used in the writeup.
#               Result: exact equality R == Q_Theta in all configurations tested.
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools

def kozlov(n): return [binomial(n,j) for j in range(1,n+1)]

def verts(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k))
            for k in range(1,len(a)+1)]

def theta_polytope(a,ds):
    n=len(a); r=len(ds); N=n+ds[-1]
    def M(p,c):   # roof of windows strictly after p (1-indexed p, coordinate c)
        return sum(a[c-d-1] for d in ds[p:] if 1<=c-d<=n)
    ieqs=[]; eqns=[]
    # Sage format: [b, a1..aN] meaning b + a.x >= 0
    def row(coeffs,b):
        v=[QQ(b)]+[QQ(coeffs.get(c,0)) for c in range(1,N+1)]; return v
    eqns.append(row({1:1},-a[0]))                       # x1 = a(1)
    for p in range(1,r+1):
        d=ds[p-1]
        jlo = 1 if p==1 else 2
        for j in range(jlo,n):
            c=d+j
            # Theta^p(c) - Theta^p(c+1) >= 0:
            # (x_c - M^p_c)/a(j) - (x_{c+1} - M^p_{c+1})/a(j+1) >= 0
            b = -M(p,c)/a[j-1] + M(p,c+1)/a[j]
            ieqs.append(row({c:1/a[j-1], c+1:-1/a[j]}, b))
    for p in range(2,r+1):
        ieqs.append(row({ds[p-1]+1:1},-a[0]))           # (Cp)
        c=ds[p-2]+n+1
        ieqs.append(row({c:-1},M(p-1,c)))               # (Dp)
    ieqs.append(row({N:1},0))                           # (F)
    return Polyhedron(ieqs=ieqs,eqns=eqns,base_ring=QQ)

def check(a,ds):
    n=len(a); N=n+ds[-1]
    Vs=[verts(a,d,N) for d in ds]
    pts=[sum(t[1:],t[0]) for t in itertools.product(*Vs)]
    R=Polyhedron(vertices=pts,base_ring=QQ)
    Q=theta_polytope(a,ds)
    ok = (Q==R)
    print("n=%d d=%-14s  Q_Theta == R : %s   (facets %d, rn=%d)"%(
        len(a),ds,ok,len([h for h in R.Hrepresentation() if h.is_inequality()]),
        len(ds)*len(a)))
    return ok

allok=True; cnt=0
for n in (2,3,4,5,6):
    a=kozlov(n)
    for r1 in (1,2,3):
        if n>=5 and r1>2: continue
        if n==2 and r1>2: continue
        for gs in itertools.product(range(1,n),repeat=r1):
            ds=[0]
            for g in gs: ds.append(ds[-1]+g)
            if n+ds[-1]>14: continue
            cnt+=1
            allok = check(a,ds) and allok
# a few deeper spot checks
for (n,ds) in [(5,[0,1,2]),(5,[0,2,4]),(5,[0,3,4]),(5,[0,1,2,3]),(6,[0,2,3]),
               (4,[0,3,6,9]),(5,[0,4,8])]:
    cnt+=1
    allok = check(kozlov(n),ds) and allok
print()
print("checked %d configurations; all equal: %s"%(cnt,allok))
