# rank2_hrep_direct_candidate.sage
#
# Changelog (reverse chronological):
#   2026-09-07  Created. A direct H-description of R at RANK TWO for the Kozlov
#               vector, stated without the Theta/Peel machinery of the rank-r
#               attempt, and verified exactly.
#
# The description: window 1's mu-chain (n-1 inequalities), window 2's mu-chain
# shifted (n-1, of which the FIRST is always redundant), the lower extra
# x(d+1) >= a(1), the upper extra x(n+1) <= roof, and x(N) >= 0.  Offsets are free
# by additivity of support functions.  Essential count (n-1) + (n-2) + 3 = 2n.
#
# Verified: the candidate set equals R exactly for n = 3,4,5,6 and every
# 1 <= d <= n-1 -- 14 configurations, and in each the unique non-facet among the
# candidates is window 2's first chain link, matching the general finding that
# window p >= 2's j = 1 link dies and the extras replace it.
#
# STATUS: this is a VERIFIED DESCRIPTION, NOT A PROOF.  Validity is free
# (additivity fixes each offset).  Completeness is the work.
#
# A route that does NOT work, recorded so it is not retried: peeling window 2
# (the shifted one) instead of window 1, which would avoid the unbounded-cylinder
# gap the adversarial review found in the general left-peel, since the leftover
# would be angle(a) itself.  Tested and it fails outright -- z is in
# shift^d(angle(a)) for none of 540 sampled points.  The reason is structural:
# angle(a) lies in the hyperplane {first coordinate = a(1)}, so any summand of a
# valid decomposition must have z(d+1) = a(1) EXACTLY, and the truncation
# z(c) = max(0, x(c) - Roof1(c)) has no reason to produce that value.  The
# left-peel gets it right only because window 2 contributes nothing at coordinate
# 1, so y(1) = x(1) = a(1) automatically.
#
# The promising independent route, not yet attempted: derive the H-description
# from the already-PROVED rank-two V-description (thm-kozlov-matrix + cor-vdesc
# give every vertex explicitly), by showing the 2n half-spaces have no vertices
# beyond those of R.  That is finite and structured at rank two, and it would be
# genuinely independent of the Theta/Peel chain.

import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def R2(a,d,N):
    V1,V2=verts(a,0,N),verts(a,d,N)
    return Polyhedron(vertices=[V1[i]+V2[j] for i in range(len(a)) for j in range(len(a))],base_ring=QQ)
print("Rank two, Kozlov: candidate H-description")
print("  window 1 chain: x(j)/a(j) >= x(j+1)/a(j+1), j=1..n-1   [n-1]")
print("  window 2 chain: same shifted, j=1..n-1                 [n-1]  (offsets by additivity)")
print("  lower extra: x(d+1) >= a(1)                            [1]")
print("  upper extra: x(n+1) <= a(1)+...                        [1]   -- total 2n")
print()
print("   n  d   facets(R)  candidate-set == R ?   which candidates are non-facets")
for n in (3,4,5,6):
  a=[binomial(n,j) for j in range(1,n+1)]
  for d in range(1,n):
    N=n+d; R=R2(a,d,N); m=n-d
    C=[]
    for sh in (0,d):
        for j in range(1,n):
            u=vector(QQ,[0]*N); u[sh+j-1]=-QQ(1)/a[j-1]; u[sh+j]=QQ(1)/a[j]; C.append(("chain%d.%d"%(sh,j),u))
    u=vector(QQ,[0]*N); u[d]=-1; C.append(("lower",u))
    if n+1<=N:
        u=vector(QQ,[0]*N); u[n]=1; C.append(("upper",u))
    u=vector(QQ,[0]*N); u[N-1]=-1; C.append(("last",u))
    eqs=[[h.b()]+list(h.A()) for h in R.Hrepresentation() if h.is_equation()]
    ieqs=[]; nonf=[]
    for nm,u in C:
        hv=max(u.dot_product(v.vector()) for v in R.vertices())
        ieqs.append([hv]+list(-u))
        F=[v.vector() for v in R.vertices() if u.dot_product(v.vector())==hv]
        if Polyhedron(vertices=F,base_ring=QQ).dim()!=R.dim()-1: nonf.append(nm)
    Q=Polyhedron(ieqs=ieqs,eqns=eqs,base_ring=QQ)
    nf=len([h for h in R.Hrepresentation() if h.is_inequality()])
    print("  %2d %2d %9d   %-20s %s"%(n,d,nf,Q==R,nonf if nonf else "-"))
