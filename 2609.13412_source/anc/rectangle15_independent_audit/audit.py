#!/usr/bin/env python3
"""Independent exact audit. Imports no code from the supplied proof bundle.
Characters: Jacobi--Trudi + induced trivial characters, not Murnaghan--Nakayama.
Swap sums: canonical concrete permutations, composed on all n actual labels;
no formula for composite marked-cycle lengths is used.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json, sys, time

if not __debug__:
    raise RuntimeError('Run the audit without Python -O or -OO; exact assertions are required.')

@cache
def parts(n, cap=None):
    if n == 0: return ((),)
    cap = n if cap is None else min(cap,n)
    return tuple((i,)+r for i in range(cap,0,-1) for r in parts(n-i,i))

@cache
def children(a):
    result=[]
    for i in range(len(a)+1):
        b=list(a)+( [0] if i==len(a) else [] )
        b[i]+=1
        if all(b[j]>=b[j+1] for j in range(len(b)-1)):
            result.append(tuple(b))
    return tuple(result)

@cache
def boxes(a):
    return frozenset((i,j) for i,m in enumerate(a) for j in range(m))

@cache
def f(a):
    if not a: return 1
    return sum(f(b) for b in parts(sum(a)-1) if boxes(b)<boxes(a))

@cache
def z(r):
    return prod(k**v*factorial(v) for k,v in Counter(r).items())

@cache
def transpose(a):
    return tuple(sum(v>=j for v in a) for j in range(1,a[0]+1)) if a else ()

@cache
def jt_h(a):
    """Expand det(h_(a_i-i+j)) into monomials of h via sparse determinant DP."""
    ell=len(a)
    dp={0:{():1}}
    for i in range(ell):
        nd={}
        for mask, poly in dp.items():
            for j in range(ell):
                if mask>>j&1: continue
                degree=a[i]-i+j
                if degree<0: continue
                sign=(-1)**sum(bool(mask>>k&1) for k in range(j+1,ell))
                dest=nd.setdefault(mask|1<<j,defaultdict(int))
                for degrees,coef in poly.items():
                    key=tuple(sorted(degrees+((degree,) if degree else ()),reverse=True))
                    dest[key]+=sign*coef
        dp={m:{p:c for p,c in pol.items() if c} for m,pol in nd.items()}
    return tuple(dp.get((1<<ell)-1,{():1}).items())

@cache
def permutation_character(capacities, rho):
    """Assign distinguishable permutation cycles to labelled row blocks."""
    if not rho: return int(not capacities)
    r=rho[0]
    out=0
    for c,m in Counter(capacities).items():
        if c<r: continue
        b=list(capacities); b.remove(c)
        if c>r: b.append(c-r)
        out+=m*permutation_character(tuple(sorted(b,reverse=True)),rho[1:])
    return out

@cache
def chi(a,rho):
    if sum(a)!=sum(rho): raise ValueError('character sizes disagree')
    if a and len(a)>a[0]:
        return (-1)**(sum(rho)-len(rho))*chi(transpose(a),rho)
    return sum(coef*permutation_character(degrees,rho) for degrees,coef in jt_h(a))

@cache
def csum(a): return sum(j-i for i,j in boxes(a))

def primitive(v):
    den=lcm(*(Fraction(t).denominator for t in v))
    ints=[int(den*t) for t in v]
    divisor=gcd(*ints)
    if divisor==0: raise ValueError('zero ray')
    return tuple(t//divisor for t in ints)

@cache
def cycle_type(p):
    seen=set(); lens=[]
    for i in range(len(p)):
        if i in seen: continue
        j=i; m=0
        while j not in seen:
            seen.add(j); m+=1; j=p[j]
        lens.append(m)
    return tuple(sorted(lens,reverse=True))

@cache
def compositions_leq(total,k):
    if k==0: return ((),)
    return tuple((i,)+rest for i in range(total+1) for rest in compositions_leq(total-i,k-1))

def representative(rho):
    p=[]; off=0
    for r in rho:
        p.extend(tuple(range(off+1,off+r))+(off,)); off+=r
    return tuple(p)

@cache
def concrete_extensions(mark_perm, n):
    """All tail/cycle orbits, explicitly realized as permutations on n labels.
    Every unmarked-label assignment orbit has size (n-k)!/z(unmarked cycles).
    """
    k=len(mark_perm); out=[]
    for tails in compositions_leq(n-k,k):
        unused=n-k-sum(tails)
        for rho in parts(unused):
            p=list(range(n)); nxt=k
            for i,t in enumerate(tails):
                chain=[i]+list(range(nxt,nxt+t))+[mark_perm[i]]
                for src,dst in zip(chain,chain[1:]): p[src]=dst
                nxt+=t
            for cyc in rho:
                for h in range(cyc): p[nxt+h]=nxt+(h+1)%cyc
                nxt+=cyc
            assert nxt==n
            p=tuple(p)
            out.append((p,cycle_type(p),factorial(n-k)//z(rho)))
    return tuple(out)

def concrete_counts(p,q,k):
    out=defaultdict(int)
    for sr in parts(k):
        s=representative(sr)
        mult=factorial(k)//z(sr)
        aa=concrete_extensions(s,p)
        for t in permutations(range(k)):
            bb=concrete_extensions(t,q)
            for a,ar,aw in aa:
                for b,br,bw in bb:
                    # Compose (a direct-sum b) after the actual cross swaps.
                    ab=a+tuple(p+j for j in b)
                    perm=list(ab)
                    for j in range(k): perm[j],perm[p+j]=ab[p+j],ab[j]
                    out[(ar,br,cycle_type(tuple(perm)))]+=mult*aw*bw
    assert sum(out.values())==factorial(p)*factorial(q)
    marginal=defaultdict(int)
    for (r,s,t),w in out.items(): marginal[r,s]+=w
    assert all(marginal[r,s]==factorial(p)//z(r)*(factorial(q)//z(s)) for r in parts(p) for s in parts(q))
    return dict(out)

def brute_counts(p,q,k):
    out=Counter()
    for a in permutations(range(p)):
        for b in permutations(range(q)):
            ab=a+tuple(p+j for j in b)
            perm=list(ab)
            for j in range(k): perm[j],perm[p+j]=ab[p+j],ab[j]
            out[(cycle_type(a),cycle_type(b),cycle_type(tuple(perm)))]+=1
    return dict(out)

def content_row(p,beta,k,ps):
    out=[]
    for nu in ps:
        if not boxes(beta)<=boxes(nu): out.append(0); continue
        added=boxes(nu)-boxes(beta)
        if len({j for i,j in added})!=p: out.append(0); continue
        def P(x): return prod(x+j-i for i,j in added)
        r=p-k
        numerator=sum((-1)**(r-j)*(factorial(r)//factorial(j)//factorial(r-j))*P(j-p+1) for j in range(r+1))
        assert numerator%factorial(r)==0
        out.append(numerator//factorial(r))
    return primitive(out)

def branch_row(beta,gamma,ps):
    assert sum(beta)==14 and sum(gamma)==13 and boxes(gamma)<boxes(beta)
    rem=next(iter(boxes(beta)-boxes(gamma))); c=rem[1]-rem[0]
    row={}
    for nu in children(beta):
        add=next(iter(boxes(nu)-boxes(beta))); diff=add[1]-add[0]-c
        assert diff!=0
        row[nu]=Fraction(1,diff)
    return primitive([row.get(nu,0) for nu in ps])

def main():
    start=time.time()
    root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent/'supplied_bundle'
    cert=json.loads((root/'certificate.json').read_text())
    assert cert['order']==15 and cert['target']==[3]*5 and cert['dimension']==6006
    assert len(cert['terms'])==125
    assert Counter(t['kind'] for t in cert['terms'])=={'central':106,'branch':19}
    assert [t['id'] for t in cert['terms']]==list(range(1,126))
    ps=parts(15); assert len(ps)==176 and tuple(map(tuple,cert['partitions']))==ps
    fs=[f(a) for a in ps]; assert f((3,)*5)==6006
    for n in range(16):
        pp=parts(n)
        table=[[chi(a,r) for r in pp] for a in pp]
        assert all(table[i][-1]==f(a) for i,a in enumerate(pp))
        weights=[factorial(n)//z(r) for r in pp]
        for i in range(len(pp)):
            for j in range(i+1):
                assert sum(x*y*w for x,y,w in zip(table[i],table[j],weights))==factorial(n)*(i==j)
    print('PASS: independent Jacobi--Trudi character tables and branching dimensions, n=0..15',flush=True)
    for p,q in [(2,3),(3,3),(3,4),(4,4)]:
        for k in range(1,min(p,q)+1):
            assert concrete_counts(p,q,k)==brute_counts(p,q,k)
    print('PASS: concrete orbit enumerator equals full permutation sums in 12 small block configurations',flush=True)
    cycle_type.cache_clear(); concrete_extensions.cache_clear()
    grouped=defaultdict(list)
    rows={}
    for term in cert['terms']:
        if term['kind']=='branch': rows[term['id']]=branch_row(tuple(term['beta']),tuple(term['gamma']),ps)
        else: grouped[(sum(term['alpha']),sum(term['beta']),term['swaps'])].append(term)
    print('PASS: 19 branching witnesses regenerated independently',flush=True)
    symmetric_checks=0
    for (p,q,k),terms in sorted(grouped.items()):
        counts=concrete_counts(p,q,k)
        for term in terms:
            a,b=tuple(term['alpha']),tuple(term['beta'])
            h=defaultdict(int)
            for (r,s,t),count in counts.items(): h[t]+=count*chi(a,r)*chi(b,s)
            raw=[sum(w*chi(nu,t) for t,w in h.items()) for nu in ps]
            rows[term['id']]=primitive(raw)
            if a==(p,):
                assert rows[term['id']]==content_row(p,b,k,ps)
                symmetric_checks+=1
            if k==1:
                for nu,val in zip(ps,raw):
                    numerator=sum(factorial(p)//z(r)*(factorial(q)//z(s))*chi(a,r)*chi(b,s)*chi(nu,tuple(sorted(r+s,reverse=True))) for r in parts(p) for s in parts(q))
                    assert numerator%(factorial(p)*factorial(q))==0
                    mult=numerator//(factorial(p)*factorial(q))
                    assert val==factorial(p)*factorial(q)//(p*q)*mult*(csum(nu)-csum(a)-csum(b))
        cycle_type.cache_clear(); concrete_extensions.cache_clear()
        print(f'PASS: independent defining character sums ({p},{q}; k={k}), {len(terms)} rows',flush=True)
    total=[0]*176
    for term in cert['terms']:
        row=rows[term['id']]
        expected={tuple(a):v for a,v in term['coefficients']}
        assert len(expected)==len(term['coefficients'])
        assert expected=={nu:v for nu,v in zip(ps,row) if v}
        assert gcd(*row)==1 and sum(v*d for v,d in zip(row,fs))==0
        weight=int(term['weight']); assert weight>0 and str(weight)==term['weight']
        for j,v in enumerate(row): total[j]+=weight*v
    M=int(cert['scale']); assert M>0
    assert gcd(M,*(int(t['weight']) for t in cert['terms']))==1
    want=[0]*176; want[ps.index((15,))]=6006*M; want[ps.index((3,)*5)]=-M
    assert total==want
    dual=json.loads((root/'old_separator.json').read_text()); assert tuple(map(tuple,dual['partitions']))==ps
    y=dual['dual_integer']
    pair=sum(r*d*yy for r,d,yy in zip(rows[120],fs,y)); assert pair==-116616500
    assert pair//50050==-2330
    print(f'PASS: {symmetric_checks} symmetric-block rows also checked by independent content-polynomial evaluations',flush=True)
    print('PASS: all 125 stored rows agree, primitive signs preserved, all weights positive, all 176 final coordinates exact',flush=True)
    print('PASS: term 120 separator pairing -116616500, normalized -2330',flush=True)
    report={'status':'PASS','independent_character_method':'Jacobi-Trudi / cycle-to-labelled-block assignment',
            'central_method':'concrete permutation representatives and direct composition on 15 labels',
            'central_rows':106,'branch_rows':19,'coordinates':176,'symmetric_content_checks':symmetric_checks,
            'nonzero_final_coordinates':[[list(p),str(t)] for p,t in zip(ps,total) if t],
            'M':str(M),'M_digits':len(str(M)),'f_target':f((3,)*5),'elapsed_seconds':time.time()-start}
    (Path(__file__).parent/'independent_results.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__': main()
