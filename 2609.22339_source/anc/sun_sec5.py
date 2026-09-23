"""Exact test of Lemma 5.3 and Corollary 5.2 (eq. 5.24) of arXiv:2609.04176 at small B.
Definitions (5.1)-(5.13) of the paper, implemented literally."""
import sys, json
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import comb, log, factorial, gcd
from itertools import combinations
from sun_lib import build_R, minor_poly
def vp(n,p):
    if n==0: return 10**9
    v=0
    while n%p==0: n//=p; v+=1
    return v
def vpq(x,p): return vp(x.numerator,p)-vp(x.denominator,p)
def primes_upto(n):
    s=bytearray([1])*(n+1); s[0:2]=b'\x00\x00'
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(3,n+1) if s[i]]
def Phi(Q,n): return sum(r//Q for r in range(n))
def N_KQ(K,Q,i): return sum(1 for h in range(1,K+1) if (2*i+2*h+1)%Q==0)
def lam(Q,A,I,B,S,N):
    C=sum((a+2*B)//Q for a in A)
    cnt={}
    for i in I: cnt[i%Q]=cnt.get(i%Q,0)+1
    coll=2*sum(comb(c,2) for c in cnt.values())
    tail=sum(2*N_KQ(B,Q,i)-N_KQ(S,Q,i)-2*(1 if Q<=2*i+1 else 0)-(i//Q+(N-1-i)//Q) for i in I)
    return C+coll+tail
def run(B,S,A,pairs=((1,2),(1,1))):
    R,Pis=build_R(B,S); N=2*B+S+3; D=2*B
    c=minor_poly(R,A,S)                     # det R[A,J] as polynomial in G (exact)
    F=1
    for r in range(D): F*=factorial(r)
    P=1
    for p in Pis[:N]: P*=p
    subsets=list(combinations(range(N),S))
    out={}
    for (a,q) in pairs:
        if gcd(a,q)!=1: continue
        val=sum(ck*Fr(a,q)**k for k,ck in enumerate(c))*Fr(q)**S      # q^S det R[A,J](a/q), exact rational
        qhat=Fr(F)*val/P/Fr(q)**S                                     # q_hat_B(a/q)
        den=(Fr(q)**S*qhat).denominator                               # true H_B^min for this pair
        viol=[]; bound_total=0.0; true_total=0.0
        for p in primes_upto(4*N+10):
            Rp=vpq(val,p); Ap=vp(P,p)-vp(F,p)
            m_sum=0; a_sum=0; Q=p
            while Q<=2*N+2*B+5:
                mQ=min(lam(Q,A,I,B,S,N) for I in subsets)
                aQ=2*sum(N_KQ(B,Q,i) for i in range(N))-Phi(Q,D)
                m_sum+=mQ; a_sum+=aQ; Q*=p
            assert a_sum==Ap, (p,a_sum,Ap)                            # check (5.13)
            true_v=max(0,Ap-Rp)                                        # [A_p - R_p]_+ = v_p(den)
            assert true_v==vp(den,p)
            bound_v=Ap-m_sum                                           # paper's (5.24) summand
            bound_total+=bound_v*log(p); true_total+=true_v*log(p)
            if Rp<m_sum: viol.append((p,Rp,m_sum,true_v,bound_v))
        out[(a,q)]=dict(log_true_den=true_total,log_paper_bound_524=bound_total,violations=viol,log_den_check=log(den) if den.bit_length()<1000 else None)
        print(f"B={B} S={S} A={A} (a,q)=({a},{q}): exact log den(q^S q_hat)={true_total:.2f} | paper's (5.24) bound={bound_total:.2f} | Lemma 5.3 violated at {len(viol)} primes")
        for p,Rp,ms,tv,bv in viol[:12]:
            print(f"     p={p:>3}: v_p(q^S det R[A,J](a/q))={Rp:>3} < sum_nu m^A_{{p^nu}}={ms:>3}   (true v_p(den)={tv}, paper's bound {bv})")
        if len(viol)>12: print("     ...")
    return out
res={}
res['20']=run(20,1,(0,))
res['21']=run(21,1,(1,))
res['25']=run(25,1,(0,))
res['30']=run(30,1,(1,))
res['40']=run(40,2,(0,1))
json.dump({k:{str(a):v for a,v in d.items()} for k,d in res.items()},open('sun_sec5.json','w'),indent=1,default=str)
