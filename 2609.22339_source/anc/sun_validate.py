import sys; sys.set_int_max_str_digits(0)
from fractions import Fraction as Fr
from math import comb, factorial, log
import mpmath as mp
sys.path.insert(0,'.')
from sun_lib import build_R, minor_poly, bareiss_det
# (1) Direct check of Prop 3.1 / q_hat formula: det A_B numerically vs F_B*minor/prod Pi
def direct(B,S,A):
    R,Pis=build_R(B,S); N=2*B+S+3; D=2*B
    Ac=[c for c in range(S+3) if c not in A]
    mp.mp.dps=400; G=mp.catalan
    part=[mp.mpf(0)]
    for m in range(1,N+S+3): part.append(part[-1]+mp.mpf((-1)**(m-1))/(2*m-1)**2)
    def u(m): return (-1)**m*(G-part[m])/(2*m+1)
    M=mp.matrix(N,N)
    for i in range(N):
        col=0
        for r in range(D): M[i,col]=mp.mpf(i**r)/Pis[i]; col+=1
        for j in range(1,S+1): M[i,col]=u(i+j); col+=1
        for ct in Ac: M[i,col]=mp.mpf(comb(i,D+ct))/Pis[i]; col+=1
    detA=mp.det(M)
    c=minor_poly(R,tuple(A),S)
    minor=sum(mp.mpf(ck.numerator)/mp.mpf(ck.denominator)*G**k for k,ck in enumerate(c))
    F=1
    for r in range(D): F*=factorial(r)
    P=1
    for p in Pis[:N]: P*=p
    formula=mp.mpf(F)*minor/mp.mpf(P)
    print(f"B={B} S={S} A={A}: det A_B = {mp.nstr(detA,15)}   F_B*minor/prodPi = {mp.nstr(formula,15)}   ratio = {mp.nstr(detA/formula,12)}")
direct(4,1,[0]); direct(4,1,[2]); direct(6,2,[0,1]); direct(6,2,[1,3]); direct(7,3,[0,2,4])
# (2) precision check at B=21,S=1: log|q_hat(G)| at dps = 3x
B,S=21,1
R,Pis=build_R(B,S); N=2*B+S+3
c=minor_poly(R,(1,),S)
F=1
for r in range(2*B): F*=factorial(r)
P=1
for p in Pis[:N]: P*=p
qc=[Fr(F)*ck/P for ck in c]
digits=max(len(str(abs(ck.numerator)))+len(str(ck.denominator)) for ck in qc)
for mult in (1,3,6):
    mp.mp.dps=digits*mult+60; G=mp.catalan
    val=sum(mp.mpf(ck.numerator)/mp.mpf(ck.denominator)*G**k for k,ck in enumerate(qc))
    print(f"B=21 S=1 A=(1,): dps={mp.mp.dps}  log|q_hat(G)| = {mp.nstr(mp.log(abs(val)),20)}")
H=1
from math import lcm
for ck in qc: H=lcm(H,ck.denominator)
print("log H_B =", log(H) if H.bit_length()<1000 else (H.bit_length()-1)*log(2)+log(H>>(H.bit_length()-60))-59*log(2))
print("coefficient denominators (bits):", [ck.denominator.bit_length() for ck in qc], " numerators (bits):", [abs(ck.numerator).bit_length() for ck in qc])

# (3) Independent interval-arithmetic enclosure of q_hat_B(G) (mpmath.iv) at the row sets of Table 1.
import json
from mpmath import iv
fin={r['B']:r for r in json.load(open('sun_final.json'))}
for B in [21,40,100,119]:
    S=fin[B]['S']; A=tuple(int(t) for t in fin[B]['best']['A'])
    R,Pis=build_R(B,S); N=2*B+S+3
    c=minor_poly(R,A,S)
    F=1
    for r in range(2*B): F*=factorial(r)
    P=1
    for p in Pis[:N]: P*=p
    qc=[Fr(F)*ck/P for ck in c]
    digits=max(len(str(abs(ck.numerator)))+len(str(ck.denominator)) for ck in qc)+60
    iv.dps=digits; G=iv.catalan
    val=iv.mpf(0)
    for k,ck in enumerate(qc): val+=iv.mpf(ck.numerator)/iv.mpf(ck.denominator)*G**k
    assert not (val.a <= 0 <= val.b), "enclosure of q_hat_B(G) contains 0"
    log_interval=iv.log(abs(val))                      # outward-rounded interval logarithm
    assert log_interval.delta < iv.mpf("1e-30"), log_interval.delta
    mp.mp.dps=50
    print(f"B={B} S={S} A={A}: certified interval for log|q_hat(G)| has width < 1e-30; rounded endpoints (18 sig. digits, display only): [{mp.nstr(mp.mpf(log_interval.a),18)}, {mp.nstr(mp.mpf(log_interval.b),18)}]  (table: {fin[B]['best']['logq']:.6f})")
