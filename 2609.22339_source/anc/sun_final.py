"""Final table for the note: exact H_B, |q_hat_B(G)| with rounding bound, S-smooth part of H_B, all row sets A."""
import sys, time, json
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import comb, lcm, log, factorial
from itertools import combinations
import mpmath as mp
from sun_lib import build_R, minor_poly
def loginth(n):  # log of a positive int
    b=n.bit_length()
    return (b-1)*log(2)+log((n>>max(0,b-64))/2**min(63,b-1))
def primes_upto(n):
    s=bytearray([1])*(n+1); s[0:2]=b'\x00\x00'
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
out=[]
for B in [21,25,30,35,39,40,50,59,60,70,79,80,90,99,100,110,119]:
    S=max(1,B//20); t0=time.time()
    R,Pis=build_R(B,S); N=2*B+S+3
    F=1
    for r in range(2*B): F*=factorial(r)
    P=1
    for p in Pis[:N]: P*=p
    rows=[]
    for A in combinations(range(S+3),S):
        c=minor_poly(R,A,S)
        if not any(c): continue
        qc=[Fr(F)*ck/P for ck in c]
        H=1
        for ck in qc: H=lcm(H,ck.denominator)
        # numeric value with explicit rounding bound
        maxc=max(abs(ck) for ck in qc)
        dig=len(str(abs(maxc.numerator)))+len(str(maxc.denominator))+80
        mp.mp.dps=dig; G=mp.catalan
        val=mp.mpf(0)
        for k,ck in enumerate(qc): val+=mp.mpf(ck.numerator)/mp.mpf(ck.denominator)*G**k
        # rounding bound: (S+1)*max|c_k|*10^{-(dps-5)}. Valid because every mpf operation is correctly rounded to the
        # working precision (mpmath semantics), |G^k|<=1, and the factor 10^5 covers the handful of operations per term.
        # An independent interval-arithmetic (mpmath.iv) evaluation of the same values is in sun_validate.py.
        logerr=log(S+1)+float(mp.log(mp.mpf(maxc.numerator)/mp.mpf(maxc.denominator)))-(dig-5)*log(10)
        lq=float(mp.log(abs(val)))
        lH=loginth(H)
        # S-smooth part of H
        sm=1; h=H
        for p in primes_upto(max(S,2)):
            while h%p==0: h//=p; sm*=p
        rows.append(dict(A=A,logH=lH,logq=lq,T=lH+lq,logerr=logerr,log_smooth_part=loginth(sm) if sm>1 else 0.0))
    rows.sort(key=lambda r:r['T'])
    best,worst=rows[0],rows[-1]
    rec=dict(B=B,S=S,N=N,nA=len(rows),best=best,worst=worst,seconds=time.time()-t0)
    out.append(rec)
    print(f"B={B:>3} S={S} N={N:>3} #A={len(rows):>2} | best: logH={best['logH']:.2f} log|q|={best['logq']:.2f} T={best['T']:.2f} T/B2={best['T']/B**2:.4f} | worst T={worst['T']:.2f} | log10 err bound={best['logerr']/log(10):.0f} vs log10|q|={best['logq']/log(10):.0f} | S-smooth part of H: log={best['log_smooth_part']:.2f} | {rec['seconds']:.0f}s",flush=True)
    json.dump(out,open('sun_final.json','w'),indent=1,default=str)
