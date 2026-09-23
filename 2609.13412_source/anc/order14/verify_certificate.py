#!/usr/bin/env python3
"""Exact independent check of the 20-witness (4433) certificate.
Python standard library only. Does not run or trust a linear-programming solver.
Uses skew-tableau linear extensions and rational Young seminormal matrices.
The arbitrary-PSD positivity argument is in PROOF.md, not encoded as a formal proof.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import factorial, isqrt
from pathlib import Path
import json

@lru_cache(None)
def partitions(n, maximum=None):
    if n == 0: return ((),)
    if maximum is None: maximum=n
    return tuple((a,)+b for a in range(min(n,maximum),0,-1)
                 for b in partitions(n-a,a))

def degree(shape):
    hp=1
    for i,row in enumerate(shape):
        for j in range(row):
            hp *= row-j+sum(x>j for x in shape[i+1:])
    return factorial(sum(shape))//hp

def contains(big, small):
    return len(big)>=len(small) and all(a>=b for a,b in zip(big,small))

@lru_cache(None)
def tableaux(eta,nu):
    """Independent of the discovery path generator: enumerate <=4 boxes."""
    if not contains(nu,eta): return ()
    boxes=tuple((i,j) for i,row in enumerate(nu)
                for j in range(eta[i] if i<len(eta) else 0,row))
    out=[]
    for seq in permutations(boxes):
        pos={box:i for i,box in enumerate(seq)}
        if all(not ((i,j-1) in pos and pos[i,j-1]>pos[i,j]) and
               not ((i-1,j) in pos and pos[i-1,j]>pos[i,j]) for i,j in boxes):
            out.append(seq)
    return tuple(out)

def prefix_shape(eta,tab,k):
    a=list(eta)+[0]*len(tab)
    for i,j in tab[:k]: a[i]+=1
    return tuple(x for x in a if x)

def trace_word(eta,nu,mu,k,word,orthogonal=False):
    tabs=tableaux(eta,nu);loc={t:i for i,t in enumerate(tabs)}
    ans=F(0)
    for t in tabs:
        if prefix_shape(eta,t,k)!=mu:continue
        # state, coefficient, radicand. For orthogonal traces, closed-path
        # radicands are exact squares; no floating-point square root is used.
        states=[(t,F(1),F(1))]
        for i in reversed(word):
            nxt=[]
            for s,c,q in states:
                d=(s[i+1][1]-s[i+1][0])-(s[i][1]-s[i][0])
                assert d != 0
                nxt.append((s,c/F(d),q))
                v=list(s);v[i],v[i+1]=v[i+1],v[i];v=tuple(v)
                if v in loc:
                    if orthogonal:nxt.append((v,c,q*(1-F(1,d*d))))
                    else:nxt.append((v,c*(1+F(1,d)),q))
            states=nxt
        for s,c,q in states:
            if s==t:
                if orthogonal:
                    a=isqrt(q.numerator);b=isqrt(q.denominator)
                    assert a*a==q.numerator and b*b==q.denominator
                    ans+=c*F(a,b)
                else:ans+=c
    return ans

def witness_coefficients(k,eta,mu,sign,orthogonal=False):
    n=sum(eta)+2*k
    row={}
    for nu in partitions(n):
        if not contains(nu,eta):continue
        if k==1:
            c=trace_word(eta,nu,mu,k,[0],orthogonal)
        elif k==2:
            tau=[1,0,2,1]
            c=(trace_word(eta,nu,mu,k,tau,orthogonal)
               +sign*trace_word(eta,nu,mu,k,[2]+tau,orthogonal))/2
        else:raise ValueError('This certificate uses only one and two contractions')
        if c:row[nu]=c
    return row

def parse_row(d):return {tuple(map(int,p.split(','))):F(c) for p,c in d.items()}

def main():
    data=json.loads(Path(__file__).with_name('certificate.json').read_text())
    n=data['order'];ps=partitions(n)
    assert len(ps)==135
    assert sum(degree(p)**2 for p in ps)==factorial(n)
    assert degree(tuple(data['target']))==12012
    aggregate={p:F(0) for p in ps};rows=[]
    for i,record in enumerate(data['rows'],1):
        k=record['k'];eta=tuple(record['eta']);mu=tuple(record['mu']);sign=record['sign']
        assert sum(eta)==n-2*k and sum(mu)==n-k
        coeff=witness_coefficients(k,eta,mu,sign)
        independently=witness_coefficients(k,eta,mu,sign,orthogonal=True)
        assert coeff==independently, ('orthogonal/seminormal disagreement',i)
        assert coeff==parse_row(record['coefficients']), ('stored row mismatch',i)
        assert sum(c*degree(p) for p,c in coeff.items())==0
        w=F(record['weight']);assert w>0
        for p,c in coeff.items():aggregate[p]+=w*c
        print('PASS witness',i,'terms',len(coeff),'weight',w)
        rows.append(coeff)
    aggregate={p:c for p,c in aggregate.items() if c}
    assert aggregate==parse_row(data['identity'])
    assert sum(c*degree(p) for p,c in aggregate.items())==0
    target=tuple(data['target'])
    assert aggregate[target]<0
    assert all(c>0 for p,c in aggregate.items() if p!=target)
    known={(6,5,3),(6,4,4),(5,5,4),(5,3,3,3)}
    assert set(aggregate)-{target}==known
    assert all(len(p)<=3 or (len(p)==4 and p[1]==p[2]) for p in known)
    print('PASS exact coefficient identity on all 135 partitions:')
    for p,c in aggregate.items():print(' ',p,c,'degree',degree(p))
    total=-aggregate[target]*degree(target)
    normalized={p:c*degree(p)/total for p,c in aggregate.items() if p!=target}
    assert sum(normalized.values())==1
    assert normalized=={(6,5,3):F(20175,238048),(6,4,4):F(20175,238048),
                        (5,5,4):F(79518,238048),(5,3,3,3):F(118180,238048)}
    def pate_covered(p):
        large=sum(x>2 for x in p)
        return large<=3 or (large==4 and p[1]==p[2])
    assert {p for p in ps if not pate_covered(p)}=={target}
    print('PASS: positive certificate, correct normalization, known-case coverage.')
    return rows

if __name__=='__main__':main()
