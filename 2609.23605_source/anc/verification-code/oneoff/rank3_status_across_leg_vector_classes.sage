# rank3_status_across_leg_vector_classes.sage
#
# Changelog (reverse chronological):
#   2026-09-07  Created, to ground the rank > 2 status table in measurement rather
#               than in relayed subagent reports.
#
# Rank 3, d = (0,1,2), four leg-vector classes.  Columns: facet count against n*s;
# whether the Theta-form cuts out R; whether the CONSECUTIVE pairwise reduction
# predicts the extremal tensor; whether the ALL-PAIRS reduction does.
#
#   strictly log-concave (Kozlov AND the tent vector i(n+1-i), identically):
#       facets = n*s,  Q_Theta = R,  consecutive OK,  all-pairs OK
#   all-ones (sigma constant):
#       facets < n*s (10 vs 12, 11 vs 15) -- Theta valid and complete but REDUNDANT
#       consecutive OK, all-pairs OK
#   log-convex (factorials):
#       facets > n*s (14 vs 12, 21 vs 15) -- OVERSHOOTS
#       Q_Theta != R,  consecutive FAILS,  all-pairs still OK
#
# Two things worth carrying: the tent vector reproduces Kozlov exactly, which is
# the rank-3 evidence that log-concavity rather than binomiality is the hypothesis;
# and the ALL-PAIRS reduction survives in every class tested, including the one
# where the consecutive sharpening is false.

import itertools
exec(open("/tmp/tight.sage").read().split('print("Does')[0])
def R_of(a,ds,N):
    return Polyhedron(vertices=[sum((verts(a,ds[i],N)[t[i]] for i in range(len(ds))),vector(QQ,[0]*N))
                      for t in itertools.product(range(len(a)),repeat=len(ds))],base_ring=QQ)
def ext(vl,N):
    idx=list(itertools.product(*[range(len(v)) for v in vl]))
    pts={t:sum((vl[k][t[k]] for k in range(len(vl))),vector(QQ,[0]*N)) for t in idx}
    P=Polyhedron(vertices=list(pts.values()),base_ring=QQ); V={tuple(v) for v in P.vertices_list()}
    return {t for t in idx if tuple(pts[t]) in V}
print("RANK 3 (d = (0,1,2)), by leg-vector class")
print("  a-class          n  facets  n*s   Q_Theta==R   consec-red   all-pairs-red")
for label,mk in (("Kozlov (slc)",lambda n:[binomial(n,j) for j in range(1,n+1)]),
                 ("tent (slc)",  lambda n:[i*(n+1-i) for i in range(1,n+1)]),
                 ("all-ones",    lambda n:[1]*n),
                 ("factorial(lx)",lambda n:[factorial(i) for i in range(1,n+1)])):
  for n in (4,5):
    a=mk(n); ds=[0,1,2]; N=n+2; r=3; s=3
    R=R_of(a,ds,N); nf=len([h for h in R.Hrepresentation() if h.is_inequality()])
    cons=theta_conditions(n,ds,N,a)
    eqs=[[h.b()]+list(h.A()) for h in R.Hrepresentation() if h.is_equation()]
    Q=Polyhedron(ieqs=[[b]+list(-u) for _,u,b in cons],eqns=eqs,base_ring=QQ)
    V=[verts(a,d,N) for d in ds]; T=ext(V,N)
    pr={(p,q):ext([V[p],V[q]],N) for p in range(3) for q in range(p+1,3)}
    U=list(itertools.product(range(n),repeat=3))
    cons_p={t for t in U if all((t[p],t[p+1]) in pr[(p,p+1)] for p in range(2))}
    all_p={t for t in U if all((t[p],t[q]) in pr[(p,q)] for p in range(3) for q in range(p+1,3))}
    print("  %-16s %d %7d %5d   %-12s %-12s %s"%(label,n,nf,n*s,Q==R,cons_p==T,all_p==T))
