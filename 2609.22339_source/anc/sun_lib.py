import sys, time
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import comb, lcm, log, lgamma
from itertools import combinations
import mpmath as mp
def logfr(x):  # log of positive Fraction via bit lengths
    n,d=abs(x.numerator),x.denominator
    return (n.bit_length()-1)*log(2)+log((n>>(max(0,n.bit_length()-64)))/2**min(63,n.bit_length()-1)) - ((d.bit_length()-1)*log(2)+log((d>>(max(0,d.bit_length()-64)))/2**min(63,d.bit_length()-1)))
def bareiss_det(M):
    M=[row[:] for row in M]; n=len(M); sign=1; prev=Fr(1)
    for k in range(n-1):
        if M[k][k]==0:
            sw=next((i for i in range(k+1,n) if M[i][k]!=0),None)
            if sw is None: return Fr(0)
            M[k],M[sw]=M[sw],M[k]; sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])/prev
        prev=M[k][k]
    return sign*M[n-1][n-1]
def lagrange(xs,ys):
    n=len(xs); coeffs=[Fr(0)]*n
    for i in range(n):
        num=[Fr(1)]; den=Fr(1)
        for j in range(n):
            if j==i: continue
            num=[ (num[k-1] if k>0 else Fr(0)) - xs[j]*(num[k] if k<len(num) else Fr(0)) for k in range(len(num)+1)]
            den*=(xs[i]-xs[j])
        for k in range(n): coeffs[k]+=ys[i]*num[k]/den
    return coeffs
def build_R(B,S):
    Mmax=(S+2)+2*B+S+2
    part=[Fr(0)]*(Mmax+2)
    for m in range(1,Mmax+2): part[m]=part[m-1]+Fr((-1)**(m-1),(2*m-1)**2)
    Pis=[]
    for i in range(2*B+S+3):
        r=1
        for h in range(1,B+1): r*=(2*(h+i)+1)**2
        Pis.append(r)
    R=[[None]*S for _ in range(S+3)]
    for a in range(S+3):
        n=a+2*B
        for j in range(1,S+1):
            cG=Fr(0); c0=Fr(0)
            for i in range(n+1):
                m=i+j
                w=Fr((-1)**(i+m)*comb(n,i)*Pis[i],2*m+1)
                cG+=w; c0-=w*part[m]
            R[a][j-1]=(c0,cG)
    return R,Pis
def minor_poly(R,A,S):
    xs=[Fr(t) for t in range(S+1)]
    ys=[]
    for t in xs:
        M=[[R[a][j][0]+R[a][j][1]*t for j in range(S)] for a in A]
        ys.append(bareiss_det(M))
    return lagrange(xs,ys)
def run(B,S,all_A=True,maxA=6):
    t0=time.time()
    R,Pis=build_R(B,S); N=2*B+S+3
    logF=sum(lgamma(r+1) for r in range(2*B))          # log prod r!
    logPi=sum(log(p) for p in Pis[:N])                  # log prod Pi_i
    rows=list(range(S+3))
    As=list(combinations(rows,S))
    if not all_A and len(As)>maxA:
        As=[As[0],As[-1]]+As[len(As)//2:len(As)//2+maxA-2]
    results=[]
    for A in As:
        c=minor_poly(R,A,S)
        if not any(c): continue
        H=1
        # q_hat coefficients = F_B * c_k / prod Pi ; H_B = lcm of denominators of these
        Fint=1
        for r in range(2*B): Fint*=__import__('math').factorial(r)
        P=1
        for p in Pis[:N]: P*=p
        qc=[Fr(Fint)*ck/P for ck in c]
        for ck in qc: H=lcm(H,ck.denominator)
        # numeric |q_hat(G)| with enough precision
        digits=max(len(str(abs(ck.numerator)))+len(str(ck.denominator)) for ck in qc)+60
        mp.mp.dps=digits
        G=mp.catalan
        val=mp.mpf(0)
        for k,ck in enumerate(qc): val+=mp.mpf(ck.numerator)/mp.mpf(ck.denominator)*G**k
        lq=float(mp.log(abs(val))) if val!=0 else float('-inf')
        lH=log(H)
        results.append((lH+lq,lH,lq,A))
    results.sort()
    best=results[0]; worst=results[-1]
    print(f"B={B:>3} S={S:>2} N={N:>3} | #A={len(results):>3} | best  T=logH+log|q|={best[0]:>12.2f} (logH={best[1]:.2f}, log|q|={best[2]:.2f}) A={best[3]} | worst T={worst[0]:.2f} | T/B^2 best={best[0]/B**2:.5f} | {time.time()-t0:.1f}s")
    sys.stdout.flush()
    return best
