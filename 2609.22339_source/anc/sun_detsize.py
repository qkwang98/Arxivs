"""Exact identity  RHS(5.24) + log|q_hat_B| = log|det R[A,J](G)| + v_2(F_D) log 2 - sum_Q m_Q log p,
and the size of det R[A,J](G) against the bound on it implied by Proposition 9.5. Inputs: sun_ranges.json."""
import json
from math import log, lgamma
rng={r['B']:r for r in json.load(open('sun_ranges.json'))}
def v2F(D): return sum(r-bin(r).count('1') for r in range(D))
rows=[]
for B,r in sorted(rng.items()):
    S=r['S']; N=2*B+S+3; D=2*B
    logF=sum(lgamma(x+1) for x in range(D)); logPi=sum(2*log(2*(h+i)+1) for i in range(N) for h in range(1,B+1))
    logdet=r['logq']-logF+logPi; v2=v2F(D)*log(2); summ=sum(r['m'].values())
    lhs=r['rhs4']+r['logq']; rhs=logdet+v2-summ; assert abs(lhs-rhs)<1e-6*abs(lhs)
    implied=-v2+summ-0.00966*B*B
    rows.append(dict(B=B,S=S,logdet_over_B2=logdet/B**2,v2log2_over_B2=v2/B**2,summ_over_B2=summ/B**2,implied_over_B2=implied/B**2,gap_over_B2=(logdet-implied)/B**2))
    print(f"B={B:>3} S={S}: log|det R(G)|/B^2={logdet/B**2:.4f}  v2(F_D)log2/B^2={v2/B**2:.4f}  sum m log p/B^2={summ/B**2:.4f}  implied bound/B^2={implied/B**2:.4f}  gap/B^2={(logdet-implied)/B**2:.4f}")
json.dump(rows,open('sun_detsize.json','w'),indent=1)
