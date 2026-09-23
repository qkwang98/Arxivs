"""Certificate for the worst-case denominator: exhibit coprime (a,q) with gcd(H_B, Phi(a,q)) small.
Phi(a,q) = sum_k x_k a^k q^{S-k}, x_k = c_k H_B. Uses the best row set A recorded in sun_final.json."""
import sys, json
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import lcm, gcd, log, factorial
from itertools import product
from sun_lib import build_R, minor_poly
def loginth(n):
    if n<=1: return 0.0
    b=n.bit_length(); return (b-1)*log(2)+log((n>>max(0,b-64))/2**min(63,b-1))
recs=json.load(open('sun_final.json'))
out=[]
for rec in recs:
    B,S=rec['B'],rec['S']; A=tuple(int(t) for t in rec['best']['A'])
    R,Pis=build_R(B,S); N=2*B+S+3
    F=1
    for r in range(2*B): F*=factorial(r)
    P=1
    for p in Pis[:N]: P*=p
    c=minor_poly(R,A,S); qc=[Fr(F)*ck/P for ck in c]
    H=1
    for ck in qc: H=lcm(H,ck.denominator)
    x=[int(ck*H) for ck in qc]; assert all(ck*H==xk for ck,xk in zip(qc,x))
    assert gcd(*x,H)==1
    # 2- and 3-adic parts of H (the only primes < S for S<=5), and best pair
    v2=0;h=H
    while h%2==0: h//=2; v2+=1
    v3=0
    while h%3==0: h//=3; v3+=1
    best=None
    for a,q in product(range(1,8),repeat=2):
        if gcd(a,q)!=1: continue
        Phi=sum(xk*a**k*q**(S-k) for k,xk in enumerate(x))
        g=gcd(H,Phi)
        if best is None or g<best[0]: best=(g,a,q)
    g,a,q=best
    out.append(dict(B=B,S=S,A=A,v2_H=v2,v3_H=v3,log_H=loginth(H),pair=(a,q),log_gcd=loginth(g),gcd=g if g<10**12 else str(g)[:40]+'...'))
    print(f"B={B:>3} S={S} A={A}: v2(H)={v2} v3(H)={v3}  log H={loginth(H):.2f} | best pair (a,q)=({a},{q}): gcd(H,Phi)={g if g<10**9 else 'big'}  log gcd={loginth(g):.3f}",flush=True)
    json.dump(out,open('sun_gcd.json','w'),indent=1,default=str)
