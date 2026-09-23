"""(a) Brute-force validation of the marginal-cost formula (7.6) for S=4,5 at small B (the formula does not depend on B).
(b) The primes N < p <= 2N+1-2S: every layer m_p equals -2S, and -sum m_p log p reproduces the paper's 4rho-2rho^2 to leading order."""
import json
from math import comb, log
from itertools import combinations
def primes_upto(n):
    s=bytearray([1])*(n+1); s[0:2]=b'\x00\x00'
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(3,n+1) if s[i]]
def N_KQ(K,Q,i): return sum(1 for h in range(1,K+1) if (2*i+2*h+1)%Q==0)
def cost(Q,i,B,S,N): return 2*N_KQ(B,Q,i)-N_KQ(S,Q,i)-2*(1 if Q<=2*i+1 else 0)-(i//Q+(N-1-i)//Q)
def m_greedy(Q,A,B,S,N):
    C=sum((a+2*B)//Q for a in A); classes={}
    for i in range(N): classes.setdefault(i%Q,[]).append(cost(Q,i,B,S,N))
    mu=[]
    for cs in classes.values():
        cs.sort(); mu+=[c+2*k for k,c in enumerate(cs)]
    mu.sort(); return C+sum(mu[:S])
def m_brute(Q,A,B,S,N):
    C=sum((a+2*B)//Q for a in A); cs=[cost(Q,i,B,S,N) for i in range(N)]; best=None
    for I in combinations(range(N),S):
        cnt={}
        for i in I: cnt[i%Q]=cnt.get(i%Q,0)+1
        v=C+2*sum(comb(c,2) for c in cnt.values())+sum(cs[i] for i in I)
        if best is None or v<best: best=v
    return best
print("(a) brute force vs (7.6):")
for B,S,A in [(9,4,(0,1,2,3)),(9,4,(1,2,4,6)),(10,5,(0,1,2,3,4)),(10,5,(2,3,4,5,7))]:
    N=2*B+S+3; bad=[]
    for p in primes_upto(2*N+2*B+5):
        Q=p
        while Q<=2*N+2*B+5:
            if m_greedy(Q,A,B,S,N)!=m_brute(Q,A,B,S,N): bad.append(Q)
            Q*=p
    print(f"   B={B} S={S} A={A}: mismatches {bad}")
print("(b) primes N < p <= 2N+1-2S:")
fin={r['B']:r for r in json.load(open('sun_final.json'))}; rho=1/20
for B in [20,40,60,80,100,119]:
    S=max(1,B//20); N=2*B+S+3; A=tuple(int(t) for t in fin[B]['best']['A'])
    ps=[p for p in primes_upto(2*N+2) if N<p<=2*N+1-2*S]
    ms=[m_greedy(p,A,B,S,N) for p in ps]
    print(f"   B={B:>3} S={S}: all m_p=-2S: {all(m==-2*S for m in ms)};  -sum m_p log p / B^2 = {-sum(m*log(p) for m,p in zip(ms,ps))/B**2:.4f}  vs 4rho-2rho^2 = {4*rho-2*rho**2:.4f}")
