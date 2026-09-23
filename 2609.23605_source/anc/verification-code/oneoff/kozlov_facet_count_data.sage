# kozlov_facet_count_data.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Supporting data for conj-kozlov-facets, and the check
#               that CORRECTED it.
#
# The conjecture was first written as "R has exactly r*n facets". That is FALSE
# for tied shifts: equal shifts give identical summands, whose walls coincide, so
# they supply the same candidates.  At d = (0,...,0) the sum is the dilation
# r*angle(a), with n facets no matter how large r is.
#
# Corrected statement, verified over 47 configurations with 0 mismatches
# (n = 3..6, ranks up to 4, patterns including ties (0,1,1), (0,0,1,1), (0,2,2,4)
# and wide gaps (0,2,4)):
#
#     facets(R) = n * s,    s = number of DISTINCT shift values.
#
# Contrast for a = (1,...,1): the count falls strictly below n*s once n >= 4 --
# deficits 1, 2, 3 at n = 4 for d = (0,1), (0,1,2), (0,1,2,3), and larger at
# n = 5 -- so genuine pruning happens there.  Any proof of the Kozlov statement
# must therefore use something specific to the Kozlov vector, not just the shape
# of angle(a).  At n = 3 the two agree, so n = 3 is NOT a discriminating test case.
#
# Also prints, for n = 4 and d = (0,1,2), each facet normal of R with its support
# value and which summands' walls it lies on -- the candidate-to-facet
# correspondence a proof would need to make explicit.

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def R_of(a,ds,N):
    return Polyhedron(vertices=[sum((verts(a,ds[i],N)[t[i]] for i in range(len(ds))),vector(QQ,[0]*N))
                      for t in itertools.product(range(len(a)),repeat=len(ds))],base_ring=QQ)
def nf(P): return len([h for h in P.Hrepresentation() if h.is_inequality()])
print("=== REFINED CLAIM: facets(R) = n * #distinct(d), Kozlov vector ===")
bad=0; tot=0
pats=[[0,0],[0,1],[0,2],[0,3],[0,0,0],[0,0,1],[0,1,1],[0,1,2],[0,0,2],[0,2,4],[0,1,3],
      [0,1,2,3],[0,1,1,2],[0,0,1,1],[0,1,1,1],[0,2,2,4]]
for n in (3,4,5,6):
  a=[binomial(n,j) for j in range(1,n+1)]
  for ds in pats:
    if len(ds)>3 and n>=5: continue
    if n>=6 and len(ds)>2: continue
    N=n+max(ds); f=nf(R_of(a,ds,N)); pred=n*len(set(ds)); tot+=1
    if f!=pred: bad+=1; print("   MISMATCH n=%d d=%s: %d vs %d"%(n,ds,f,pred))
print("   %d configurations, %d mismatches"%(tot,bad))
print("\n=== CONTRAST: all-ones, same configurations ===")
print("   n  d-vector        n*#distinct  facets(R)  deficit")
for n in (3,4,5):
  a=[1]*n
  for ds in ([0,1],[0,2],[0,1,2],[0,1,3],[0,1,2,3]):
    if len(ds)>3 and n==5: continue
    N=n+max(ds); f=nf(R_of(a,ds,N)); pred=n*len(set(ds))
    print("   %d  %-14s %8d %10d %8d"%(n,ds,pred,f,pred-f))
print("\n=== which candidate walls survive: correspondence for n=4, d=(0,1,2) Kozlov ===")
n=4; a=[binomial(n,j) for j in range(1,n+1)]; ds=[0,1,2]; N=n+max(ds)
R=R_of(a,ds,N); S=[Polyhedron(vertices=verts(a,d,N),base_ring=QQ) for d in ds]
def h(P,u): return max(u.dot_product(v.vector()) for v in P.vertices())
for hh in R.Hrepresentation():
    if not hh.is_inequality(): continue
    u=-vector(QQ,hh.A()); g=gcd([x for x in u if x!=0]); u=u/g
    w=[i+1 for i,P in enumerate(S)
       if Polyhedron(vertices=[v.vector() for v in P.vertices() if u.dot_product(v.vector())==h(P,u)],
                     base_ring=QQ).dim()>=1]
    print("   u=%-26s h=%-5s walls of summands %s"%(tuple(u),h(R,u),w))
