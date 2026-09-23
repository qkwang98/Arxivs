"""Verify all finite/symbolic certificates used by proof.md.
The general representation-theoretic and combinatorial proofs are in proof.md.
This verifier checks the infinite-family symbolic sign certificate, independent
finite-difference cross-checks, balance, and exact node-closure enumeration.
"""
import json
from pathlib import Path
from core import partitions, dimension, witness
from structural import (longrow,max_corner,old_seed,new_seed,node_closure,
                         analytic_old,analytic_new)
from polynomials import P,family_DE
from verify_symbolic import verify as symbolic

HERE=Path(__file__).resolve().parent

def main():
    symbolic()
    count=0
    for q in range(1,19):
        for rho in partitions(q):
            C=max_corner(rho);m=max(rho[0],q+C-1);lam=(m,)+rho
            rr=witness(m,rho,1)
            assert rr[lam]==-q
            assert all(v>=0 and longrow(nu) for nu,v in rr.items() if nu!=lam)
            assert sum(dimension(nu)*v for nu,v in rr.items())==0
            if m>rho[0]:
                smaller=witness(m-1,rho,1)
                assert any(v<0 for nu,v in smaller.items() if nu!=(m-1,)+rho)
            count+=1
    print(f'PASS: {count} independent exact long-row examples, sharp coefficient thresholds, hereditary tests, balances.')
    a,b,g=[P.var(i) for i in range(3)]
    polys=[family_DE(a,b,g,c) for c in range(4)]
    coordinates=0;families=0;good=0
    for bv in range(4,15):
        for av in range(bv,2*bv+5):
            dr=witness(bv,(av,3,3),3);er=witness(av,(bv,3,3),1)
            dr2={};er2={};hr={}
            w1=2*bv+4-av;w2=bv*(bv+1)*(3*av-4*bv+4)
            for gv in range(bv-2):
                for c in range(4):
                    nu=tuple(v for v in (av+bv-gv-c,gv+3,3,c) if v)
                    D,E=[p.value(av,bv,gv) for p in polys[c]]
                    assert D.denominator==E.denominator==1
                    if D:dr2[nu]=D.numerator
                    if E:er2[nu]=E.numerator
                    hr[nu]=w1*D+w2*E
                    coordinates+=1
            assert dr==dr2 and er==er2
            T=2*bv*(bv+1)*(bv+8)*(av-bv+2)
            target=(av,bv,3,3)
            assert hr[target]==-T
            assert sum(dimension(nu)*v for nu,v in hr.items())==0
            if 5*av>=8*bv:
                assert w1>=0 and w2>0
                assert all(v>=0 for nu,v in hr.items() if nu!=target)
                good+=1
            families+=1
    print(f'PASS: {coordinates} coefficient pairs in {families} parameter instances match the independent finite-difference formula.')
    print(f'PASS: {good} instances of the uniform two-witness region; exact target coefficients and convex balances.')
    records=json.loads((HERE/'frontier_counts.json').read_text())
    residual=json.loads((HERE/'residual_shapes.json').read_text())
    total=0
    for r in records:
        n=r['n'];ps=partitions(n);old=node_closure(n,old_seed);new=node_closure(n,new_seed)
        assert all((lam in old)==analytic_old(lam) for lam in ps)
        assert all((lam in new)==analytic_new(lam) for lam in ps)
        rem=[lam for lam in ps if lam not in new]
        assert [list(lam) for lam in rem]==residual[str(n)]
        assert len(ps)==r['partitions'] and len(old)==r['old_covered'] and len(new)==r['new_covered']
        assert len(rem)==r['residual'] and len(new-old)==r['newly_covered']
        assert sum(sum(x>=3 for x in lam)==4 for lam in rem)==r['residual_4large']
        assert sum(sum(x>=3 for x in lam)>=5 for lam in rem)==r['residual_ge5large']
        total+=len(ps)
    print(f'PASS: all {total} partitions in orders 16..30; graph node-closure equals the structural predicates.')
    # Exact failure of a tempting, stronger but false coefficient-sign ansatz.
    av,bv,gv=170,112,101
    D,E=[p.value(av,bv,gv) for p in polys[3]]
    H=(2*bv+4-av)*D+bv*(bv+1)*(3*av-4*bv+4)*E
    assert H==-19169472
    print('PASS: rejected slope-3/2 coefficient ansatz has exact negative coordinate -19169472.')
    print('ALL EXACT CHECKS PASSED.')

if __name__=='__main__':main()
