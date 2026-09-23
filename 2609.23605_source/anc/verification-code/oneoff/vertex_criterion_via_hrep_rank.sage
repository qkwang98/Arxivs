# vertex_criterion_via_hrep_rank.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Tests whether the Theta-form H-description yields the
#               extremal tensor, and locates exactly where the leg vector enters.
#
# Jan asked whether a concrete H-description "automatically" gives the extremal
# tensor. It does not -- rn facets cannot cheaply encode n^r data, and H -> V is
# vertex enumeration, not Fourier-Motzkin -- but it does give an exact criterion:
#
#     M[j] = 1  <=>  rank{ Theta-normals tight at sum_p v(p,j(p)) } + e(1) = N.
#
# Verified exactly, for BOTH leg vectors: 64/64, 125/125, 25/25, 16/16.
#
# A wrong model, recorded because it is the natural first guess.  Every Theta
# normal is supported on at most two ADJACENT coordinates, so one expects the
# tight set to be a subgraph of a path and rank = N - #(components without an
# anchor).  That is FALSE, because a path admits no cycles but does admit
# PARALLEL EDGES: two different windows can both contribute a link on the same
# coordinate pair (c, c+1).  Parallel links add rank only if independent.
#
# And that is exactly where the leg vector enters.  A link from window p on the
# pair (c, c+1) has component ratio a(c+1-d(p)) / a(c-d(p)).  Two such links are
# PARALLEL iff those ratios agree.  For a = (1,...,1) the ratio is 1 always, so
# every parallel pair is dependent.  For the Kozlov vector the ratio is
# a(i+1)/a(i) = (n-i)/(i+1), strictly decreasing hence INJECTIVE in i, so the
# ratios agree only when d(p) = d(p'): for distinct shifts, never parallel.
#
# Measured: Kozlov 0 dependent / k independent; all-ones k dependent / 0
# independent, in every configuration.  This is the same injectivity of the
# slopes (n-j)/(j+1) that the conj-kozlov-facets note uses for irredundancy on
# the H-side, now seen to drive the V-side too.

import itertools
exec(open("/tmp/tight.sage").read().split('print("Does')[0])
def study(n,ds,a,label):
    N=n+max(ds); r=len(ds); cons=theta_conditions(n,ds,N,a)
    V=[verts(a,d,N) for d in ds]
    pts={t:sum((V[i][t[i]] for i in range(r)),vector(QQ,[0]*N)) for t in itertools.product(range(n),repeat=r)}
    P=Polyhedron(vertices=list(pts.values()),base_ring=QQ)
    VS={tuple(v) for v in P.vertices_list()}
    Mt={t for t in pts if tuple(pts[t]) in VS}
    e1=vector(QQ,[1]+[0]*(N-1)); ok=0
    for t,x in pts.items():
        T=[u for nm,u,b in cons if u.dot_product(x)==b]
        ok += ((matrix(QQ,[e1]+T).rank()==N)==(t in Mt))
    # do any two conditions share a coordinate pair, and are they parallel?
    par=[]; indep=[]
    supp={}
    for nm,u,b in cons:
        s=tuple(i for i,y in enumerate(u) if y!=0)
        supp.setdefault(s,[]).append((nm,u))
    for s,lst in supp.items():
        if len(s)==2 and len(lst)>1:
            for (n1,u1),(n2,u2) in itertools.combinations(lst,2):
                (par if matrix(QQ,[u1,u2]).rank()==1 else indep).append((n1,n2,s))
    print("  %-8s n=%d d=%-10s rank-test %d/%d   parallel-support pairs: %d dependent, %d independent   |M=1|=%d"
          %(label,n,ds,ok,n**r,len(par),len(indep),len(Mt)))
    return len(Mt)
print("Where does the leg vector enter the rank criterion?")
for n,ds in ((4,[0,1,2]),(5,[0,1,2]),(5,[0,1]),(4,[0,1])):
    k=study(n,ds,[binomial(n,j) for j in range(1,n+1)],"kozlov")
    o=study(n,ds,[1]*n,"ones")
    print("      -> Kozlov has %d more extremal tuples than all-ones\n"%(k-o))
