import sys
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import comb
from itertools import combinations
import mpmath as mp
mp.mp.dps=80
G=mp.catalan
# --- polynomial helpers over Q (list of Fractions, index = degree)
def padd(p,q):
    n=max(len(p),len(q)); r=[Fr(0)]*n
    for i,c in enumerate(p): r[i]+=c
    for i,c in enumerate(q): r[i]+=c
    return ptrim(r)
def pmul(p,q):
    if not p or not q: return []
    r=[Fr(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        if a==0: continue
        for j,b in enumerate(q): r[i+j]+=a*b
    return ptrim(r)
def ptrim(p):
    while p and p[-1]==0: p.pop()
    return p
def pneg(p): return [-c for c in p]
def pdet(M):
    n=len(M)
    if n==1: return M[0][0]
    if n==2: return padd(pmul(M[0][0],M[1][1]),pneg(pmul(M[0][1],M[1][0])))
    r=[]
    for c in range(n):
        minor=[row[:c]+row[c+1:] for row in M[1:]]
        term=pmul(M[0][c],pdet(minor))
        r=padd(r,term if c%2==0 else pneg(term))
    return r
def peval(p,x): return sum(mp.mpf(c.numerator)/mp.mpf(c.denominator)*x**i for i,c in enumerate(p))
def pgcd(p,q):
    p=list(p); q=list(q)
    while q:
        # p mod q
        while p and len(p)>=len(q):
            f=p[-1]/q[-1]; d=len(p)-len(q)
            for i,c in enumerate(q): p[i+d]-=f*c
            ptrim(p)
        p,q=q,p
    if p:
        lead=p[-1]; p=[c/lead for c in p]
    return p
# --- Sun's matrix
def Smat(B,S):
    # S_{m-1} partial sums, needed up to m = (S+2)+2B + S
    Mmax=(S+2)+2*B+S+2
    part=[Fr(0)]*(Mmax+2)  # part[m] = S_{m-1} = sum_{k<m} (-1)^k/(2k+1)^2
    for m in range(1,Mmax+2): part[m]=part[m-1]+Fr((-1)**(m-1),(2*m-1)**2)
    def Pi(i):
        r=Fr(1)
        for h in range(1,B+1): r*=(2*(h+i)+1)**2
        return r
    Pis=[Pi(i) for i in range(2*B+S+3)]
    R=[[None]*S for _ in range(S+3)]
    for a in range(S+3):
        n=a+2*B
        for j in range(1,S+1):
            cG=Fr(0); c0=Fr(0)
            for i in range(n+1):
                m=i+j
                w=Fr((-1)**i*comb(n,i))*Pis[i]*Fr((-1)**m,2*m+1)   # u_m = (-1)^m (G - S_{m-1})/(2m+1)
                cG+=w; c0-=w*part[m]
            R[a][j-1]=ptrim([c0,cG])
    return R
def analyse(B,S):
    R=Smat(B,S)
    rows=range(S+3)
    minors=[]
    for A in combinations(rows,S):
        M=[R[a] for a in A]
        minors.append((A,pdet(M)))
    nonzero=[(A,p) for A,p in minors if p]
    generic_rank_full = len(nonzero)>0
    g=[]
    for A,p in nonzero: g=pgcd(g,p) if g else [c/p[-1] for c in p]
    # numeric diagnostic at true G: Hadamard-normalised size of the largest minor (|det| / product of column norms <= 1).
    # The entries alpha+beta*G cancel massively, so the working precision must exceed the digit count of the
    # coefficients; otherwise this column is garbage (an earlier version printed ratios > 1 for that reason).
    digits=max(len(str(abs(c.numerator)))+len(str(c.denominator)) for A,p in nonzero for row in (R[a] for a in A) for e in row for c in e)+60
    mp.mp.dps=digits; G=mp.catalan
    best=mp.mpf(0)
    for A,p in nonzero:
        val=abs(peval(p,G))
        M=[R[a] for a in A]
        colnorm=mp.mpf(1)
        for j in range(S):
            colnorm*=mp.sqrt(sum(peval(M[i][j],G)**2 for i in range(S)))
        ratio=val/colnorm if colnorm>0 else mp.mpf(0)
        assert ratio<=1+mp.mpf(10)**(-20), ratio
        if ratio>best: best=ratio
    return generic_rank_full, len(nonzero), len(minors), len(g)-1 if g else None, best
print(f"{'B':>3} {'S':>2} | generic rank=S | nonzero minors | deg gcd(minors) | best Hadamard ratio at G (<=1; diagnostic only)")
for S in [1,2,3,4]:
    for B in list(range(S+1,min(S+1+6,31)))+[12,16,20,25,30]:
        if B<=S: continue
        gr,nz,tot,dg,best=analyse(B,S)
        print(f"{B:>3} {S:>2} | {str(gr):>14} | {nz:>3}/{tot:<3}      | {dg!s:>15} | {mp.nstr(best,6)}")
        sys.stdout.flush()
