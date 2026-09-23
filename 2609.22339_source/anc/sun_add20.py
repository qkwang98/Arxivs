"""Append B=20 (S=1) to sun_final.json using the same procedure as sun_final.py."""
import sys, json, time
sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import lcm, log, factorial
from itertools import combinations
import mpmath as mp
from sun_lib import build_R, minor_poly
def loginth(n):
    b=n.bit_length(); return (b-1)*log(2)+log((n>>max(0,b-64))/2**min(63,b-1))
B,S=20,1; t0=time.time()
R,Pis=build_R(B,S); N=2*B+S+3
F=1
for r in range(2*B): F*=factorial(r)
P=1
for p in Pis[:N]: P*=p
rows=[]
for A in combinations(range(S+3),S):
    c=minor_poly(R,A,S); qc=[Fr(F)*ck/P for ck in c]
    H=1
    for ck in qc: H=lcm(H,ck.denominator)
    maxc=max(abs(ck) for ck in qc); dig=len(str(abs(maxc.numerator)))+len(str(maxc.denominator))+80
    mp.mp.dps=dig; G=mp.catalan
    val=sum(mp.mpf(ck.numerator)/mp.mpf(ck.denominator)*G**k for k,ck in enumerate(qc))
    logerr=log(S+1)+float(mp.log(mp.mpf(maxc.numerator)/mp.mpf(maxc.denominator)))-(dig-5)*log(10)
    rows.append(dict(A=A,logH=loginth(H),logq=float(mp.log(abs(val))),T=loginth(H)+float(mp.log(abs(val))),logerr=logerr,log_smooth_part=0.0))
rows.sort(key=lambda r:r['T'])
rec=dict(B=B,S=S,N=N,nA=len(rows),best=rows[0],worst=rows[-1],seconds=time.time()-t0)
out=json.load(open('sun_final.json'))
out=[r for r in out if r['B']!=20]; out.insert(0,rec)
json.dump(out,open('sun_final.json','w'),indent=1,default=str)
print("B=20 added:", rec['best']['T'], rec['best']['A'], "worst", rec['worst']['T'])
