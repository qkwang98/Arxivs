"""Exact per-range sums of the paper's local layers m^A_{Q,B} and a_{Q,B} (defs (5.7),(5.8),(5.12)),
compared with the limits asserted in Sections 6-8: middle primes -> Lambda_mid, large primes -> -4rho/3-5rho^2/4.
m_Q via the marginal-cost formula (7.6) (greedy over residue classes), cross-checked by brute force for S<=3."""
import sys, json
sys.set_int_max_str_digits(0)
from math import comb, log
from itertools import combinations
def primes_upto(n):
    s=bytearray([1])*(n+1); s[0:2]=b'\x00\x00'
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(3,n+1) if s[i]]
def Phi(Q,n): return sum(r//Q for r in range(n))
def N_KQ(K,Q,i): return sum(1 for h in range(1,K+1) if (2*i+2*h+1)%Q==0)
def cost(Q,i,B,S,N): return 2*N_KQ(B,Q,i)-N_KQ(S,Q,i)-2*(1 if Q<=2*i+1 else 0)-(i//Q+(N-1-i)//Q)
def m_greedy(Q,A,B,S,N):
    C=sum((a+2*B)//Q for a in A)
    classes={}
    for i in range(N): classes.setdefault(i%Q,[]).append(cost(Q,i,B,S,N))
    mu=[]
    for r,cs in classes.items():
        cs.sort()
        for k,c in enumerate(cs): mu.append(c+2*k)
    mu.sort(); return C+sum(mu[:S])
def m_brute(Q,A,B,S,N):
    C=sum((a+2*B)//Q for a in A); best=None
    cs=[cost(Q,i,B,S,N) for i in range(N)]
    for I in combinations(range(N),S):
        cnt={}
        for i in I: cnt[i%Q]=cnt.get(i%Q,0)+1
        v=C+2*sum(comb(c,2) for c in cnt.values())+sum(cs[i] for i in I)
        if best is None or v<best: best=v
    return best
fin={r['B']:r for r in json.load(open('sun_final.json'))}
rho=1/20; Lam_mid=0.1763558379286483; large_lim=-4*rho/3-5*rho**2/4
print(f"paper: Lambda_mid={Lam_mid:.5f} (middle primes S<p<=B),  large-prime limit -4rho/3-5rho^2/4={large_lim:.5f} (B<p<=(2+rho)B)")
print(f"{'B':>3} {'S':>2} | {'sum m: Q<=S':>11} {'S<p<=B':>9} {'B<p<=2.05B':>10} {'p>2.05B':>8} {'hi powers':>9} | {'sum a: Q<=S':>11} {'S<p<=B':>9} {'p>B':>8} {'hi pow':>7} | {'RHS(4)/B^2':>10} {'log|q|/B^2':>10} {'total/B^2':>9}")
out=[]
for B in [20,21,25,30,40,60,80,100,119]:
    S=max(1,B//20); N=2*B+S+3; A=tuple(int(t) for t in fin[B]['best']['A'])
    Qmax=2*N+2*B+5
    sums={'m':{'small':0.0,'mid':0.0,'large':0.0,'vlarge':0.0,'hi':0.0},'a':{'small':0.0,'mid':0.0,'large':0.0,'hi':0.0}}
    checked=0
    for p in primes_upto(Qmax):
        Q=p; nu=1
        while Q<=Qmax:
            mQ=m_greedy(Q,A,B,S,N); aQ=2*sum(N_KQ(B,Q,i) for i in range(N))-Phi(Q,2*B)
            if S<=3 and checked<40 and Q>S and Q%7==3:
                assert mQ==m_brute(Q,A,B,S,N),(B,Q); checked+=1
            w=log(p)
            if Q<=S: sums['m']['small']+=mQ*w; sums['a']['small']+=aQ*w
            elif nu>=2: sums['m']['hi']+=mQ*w; sums['a']['hi']+=aQ*w
            elif Q<=B: sums['m']['mid']+=mQ*w; sums['a']['mid']+=aQ*w
            else:
                sums['a']['large']+=aQ*w
                if Q<=(2+rho)*B: sums['m']['large']+=mQ*w
                else: sums['m']['vlarge']+=mQ*w
            Q*=p; nu+=1
    B2=B*B; m=sums['m']; a=sums['a']
    rhs4=sum(a.values())-sum(m.values())
    lq=fin[B]['best']['logq']
    print(f"{B:>3} {S:>2} | {m['small']/B2:11.4f} {m['mid']/B2:9.4f} {m['large']/B2:10.4f} {m['vlarge']/B2:8.4f} {m['hi']/B2:9.4f} | {a['small']/B2:11.4f} {a['mid']/B2:9.4f} {a['large']/B2:8.4f} {a['hi']/B2:7.4f} | {rhs4/B2:10.4f} {lq/B2:10.4f} {(rhs4+lq)/B2:9.4f}", flush=True)
    out.append(dict(B=B,S=S,A=A,m=m,a=a,rhs4=rhs4,logq=lq,brute_checks=checked))
json.dump(out,open('sun_ranges.json','w'),indent=1)
