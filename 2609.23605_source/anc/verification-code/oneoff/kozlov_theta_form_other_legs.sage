# kozlov_theta_form_other_legs.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Probes the SCOPE of the Theta-form H-description of
#               working-notes/conj-kozlov-facets-attempt.org beyond the Kozlov
#               vector.  Results (recorded, since they shaped the writeup):
#               * all-ones a=(1,..,1): Q_Theta == R in all 15 configs tried
#                 (n=3..5, r<=4) -- the system stays VALID and COMPLETE, just
#                 redundant, and counting distinct directions reproduces the
#                 n+d+2 of conj-ones-hrep at rank two.  Road to that conjecture.
#               * 40 random positive leg vectors, 120 configs (n=3..5): 45
#                 mismatches, EVERY one of the form R not-subset Q_Theta
#                 (validity fails: Theta offsets undershoot the support values
#                 when Lemma D's ratio monotonicity flips) while Q_Theta subset R
#                 held in every failure.  So the peel direction is robust; the
#                 validity direction is where the Kozlov vector's increasing
#                 rho is genuinely load-bearing.
#
# Depends on theta_polytope()/verts() from kozlov_hrep_theta_form_check.sage
# (loaded below; that file re-runs its own Kozlov grid first, which is fine).
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

load("code/oneoff/kozlov_hrep_theta_form_check.sage")
import itertools

def R_of(a,ds):
    n=len(a); N=n+max(ds)
    Vs=[verts(a,d,N) for d in ds]
    pts=[sum(t[1:],t[0]) for t in itertools.product(*Vs)]
    return Polyhedron(vertices=pts,base_ring=QQ)

print("\n=== all-ones leg vector (weak ratio monotonicity) ===")
allok=True
for n in (3,4,5):
    a=[1]*n
    for ds in ([0,1],[0,2],[0,1,2],[0,1,3],[0,2,3],[0,1,2,3]):
        if max(ds)>n-1: continue
        R=R_of(a,ds); Q=theta_polytope(a,ds)
        ok=(Q==R); allok=allok and ok
        print("ALLONES n=%d d=%-12s Q_Theta == R : %s (facets %d, rn=%d)"%(n,ds,ok,
              len([h for h in R.Hrepresentation() if h.is_inequality()]),len(ds)*n))
print("all-ones all equal:",allok)

print("\n=== random positive leg vectors: which inclusion breaks? ===")
set_random_seed(1234)
tot=0; mism=0; always_QsubR=True
for trial in range(40):
    n=ZZ.random_element(3,6)
    a=[ZZ.random_element(1,9) for _ in range(n)]
    for ds in ([0,1],[0,2],[0,1,2]):
        if max(ds)>n-1: continue
        tot+=1
        R=R_of(a,ds); Q=theta_polytope(a,ds)
        if Q!=R:
            mism+=1
            RsubQ=all(Q.contains(v.vector()) for v in R.vertices())
            QsubR=all(R.contains(v.vector()) for v in Q.vertices())
            always_QsubR = always_QsubR and QsubR
            print("  MISMATCH a=%s d=%s  RsubQ=%s QsubR=%s"%(a,ds,RsubQ,QsubR))
print("tested %d; mismatches %d; Q_Theta subset R in every mismatch: %s"%(
      tot,mism,always_QsubR))
