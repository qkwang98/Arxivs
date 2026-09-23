# kozlov_generating_functions.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Tests whether multiplying the generating function of the
#               achievable Hilbert functions by the Kozlov-vertex denominator
#               prod_j (1 - x^{v_j}) simplifies it.  It does not, at rank 1 or 2.
#               Reformulates by rank and finds the deficiency formulas.
#
# Companion to working-notes/generating-functions-and-the-kozlov-denominator.org,
# which carries the discussion.  Headline results:
#   * rank 1, n = 4: P has 16 terms, P*D has 239, coefficients in [-4,3]; P is
#     divisible by no single factor (1 - x^{v_j}).  The hypothesis fails, and had
#     to: the achievable set is FINITE, so P is a polynomial with no denominator.
#   * rank 2, n = 4, d = 1: 162 terms -> 109356.  Using the true vertex set of
#     Koz(n;0,d) from thm-kozlov-matrix rather than all n^2 sums does not help.
#   * Graded by RANK the intuition is right: a(r) = |r-fold sumset| is eventually
#     polynomial (Khovanskii), degree n-1, so sum a(r) t^r is rational.
#   * n = 3: a(r) = e(r) = (r+1)(3r+2)/2 -- every lattice point achievable.
#   * n = 4: a(r) = (r+1)(4r^2+3r+1), e(r) = (r+1)^2(4r+1), deficiency exactly
#     2r(r+1), confirmed r = 1..6.  This is Part III's question with an answer.
#   * n = 5: deficiency 92, 481, 1372 -- no formula found, too few data points.
#   * The 2-graded generating function factors exactly: P2(x,y) = P(x)P(y).
#
# Cross-checks: the Kruskal-Katona enumeration agrees with exhaustive enumeration
# of downward-closed families (n = 3, 4), and with Macaulay2 (25 / 16 at n = 4);
# the proper counts 5, 16, 70, 457 reproduce |S(n)| from counting-ff-vectors.org.
#
# OEIS, checked 2026-09-06 via Sage's interface (closed forms agree, so these are
# real identifications and not prefix coincidences):
#   n=3 a(r)=e(r) ............ A000326, pentagonal numbers (ours is the (r+1)-st)
#   n=4 e(r) ................. A103532, d(240^n) = (4n+1)(n+1)^2, same closed form
#   n=4 deficiency ........... A046092, 2m(m+1)
#   n=4 a(r) ................. NO MATCH -- genuine submission candidate
# Not submitted, and not to be submitted without Jan's decision, per policy.

import itertools
from itertools import combinations

# ---- achievable Hilbert functions of E_n/I via Kruskal-Katona -------------
def canon(m, i):
    """i-canonical representation of m: m = C(a_i,i)+C(a_{i-1},i-1)+..."""
    out=[]
    for k in range(i,0,-1):
        if m<=0: break
        a=k-1
        while binomial(a+1,k)<=m: a+=1
        out.append((a,k)); m-=binomial(a,k)
    return out
def kk_bound(m,i):
    """max possible h_{i+1} given h_i = m (Kruskal-Katona pseudopower)."""
    if m<=0: return 0
    return sum(binomial(a,k+1) for (a,k) in canon(m,i))

def achievable(n, proper):
    """All (h_1,...,h_n) that are f-vectors of a complex on [n]; proper => h_1=n."""
    res=[]
    def rec(j, h):
        if j>n: res.append(tuple(h)); return
        lo, hi = 0, min(binomial(n,j), kk_bound(h[-1], j-1) if j>1 else n)
        if j==1: lo,hi = (n,n) if proper else (0,n)
        for v in range(lo,hi+1):
            if j>1 and v>kk_bound(h[-1],j-1): continue
            rec(j+1, h+[v])
    rec(1,[])
    return sorted(set(res))

# brute-force check for small n
def brute(n, proper):
    mons=[frozenset(s) for k in range(n+1) for s in combinations(range(1,n+1),k)]
    out=set()
    for mask in range(1<<len(mons)):
        fam={mons[i] for i in range(len(mons)) if mask>>i&1}
        if not all(frozenset(t) in fam for s in fam for k in range(len(s)) for t in combinations(s,k)): continue
        if frozenset() not in fam: continue
        h=tuple(sum(1 for s in fam if len(s)==j) for j in range(1,n+1))
        if proper and h[0]!=n: continue
        out.add(h)
    return sorted(out)

for n in (3,4):
    for pr in (True,False):
        a=achievable(n,pr); b=brute(n,pr)
        print("n=%d proper=%-5s  KK-enum %3d   brute %3d   agree %s"%(n,pr,len(a),len(b),a==b))
print()
for n in (3,4,5,6):
    print("n=%d: proper %4d, all %4d achievable Hilbert functions"
          %(n,len(achievable(n,True)),len(achievable(n,False))))

# ---- generating functions, rank-graded counts, item 2, 2-graded ----
def Hp(n): return [vector(ZZ,h) for h in achievable(n,True)]
def sumset(n,r,H=None):
    H=H or Hp(n); S={tuple(h) for h in H}
    for _ in range(r-1): S={tuple(vector(ZZ,s)+h) for s in S for h in H}
    return S
def Koz(n):
    c=[binomial(n,i) for i in range(1,n+1)]
    return Polyhedron(vertices=[vector(QQ,c[:j]+[0]*(n-j)) for j in range(1,n+1)],base_ring=QQ)

print("=== confirm the deficiency formulas ===")
print("  n=3: predicted missing 0;  n=4: predicted missing 2r(r+1)")
for n,rmax in ((3,7),(4,6),(5,3)):
    K=Koz(n)
    for r in range(1,rmax+1):
        a=len(sumset(n,r)); e=len((r*K).integral_points())
        pred = 0 if n==3 else (2*r*(r+1) if n==4 else None)
        tag = "" if pred is None else ("  matches 2r(r+1)" if e-a==pred else "  *** MISMATCH ***")
        print("   n=%d r=%d: a_r=%6d  e_r=%6d  missing=%5d%s"%(n,r,a,e,e-a,tag))

print("\n=== item 2: rank two with a shift; denominator from the ACTUAL vertices ===")
for n in (3,4):
  for d in (1,2):
    N=n+d
    H=Hp(n)
    S={tuple(vector(ZZ,list(h)+[0]*d)+vector(ZZ,[0]*d+list(g))) for h in H for g in H}
    R=PolynomialRing(ZZ,['x%d'%i for i in range(1,N+1)]); X=R.gens()
    P=sum(prod(X[i]**s[i] for i in range(N)) for s in S)
    c=[binomial(n,i) for i in range(1,n+1)]
    vs=[vector(QQ,list(c[:j])+[0]*(n-j)) for j in range(1,n+1)]
    pts=[vector(QQ,list(u)+[0]*d)+vector(QQ,[0]*d+list(w)) for u in vs for w in vs]
    Q=Polyhedron(vertices=pts,base_ring=QQ)
    D=prod(1-prod(X[i]**ZZ(v[i]) for i in range(N)) for v in Q.vertices_list())
    Nu=P*D
    print("   n=%d d=%d: |sumset|=%4d  vertices(Koz(n;0,d))=%2d  terms(P)=%4d -> terms(P*D)=%6d"
          %(n,d,len(S),len(Q.vertices()),len(P.monomials()),len(Nu.monomials())))

print("\n=== the 2-graded generating function factors (product structure) ===")
for n in (3,4):
    H=achievable(n,True)
    R=PolynomialRing(ZZ,['x%d'%i for i in range(1,n+1)]+['y%d'%i for i in range(1,n+1)])
    X=R.gens()[:n]; Y=R.gens()[n:]
    Px=sum(prod(X[i]**h[i] for i in range(n)) for h in H)
    Py=sum(prod(Y[i]**h[i] for i in range(n)) for h in H)
    P2=sum(prod(X[i]**h[i] for i in range(n))*prod(Y[i]**g[i] for i in range(n)) for h in H for g in H)
    print("   n=%d: P2 == Px*Py ?  %s   (terms: %d = %d x %d)"
          %(n,P2==Px*Py,len(P2.monomials()),len(Px.monomials()),len(Py.monomials())))
