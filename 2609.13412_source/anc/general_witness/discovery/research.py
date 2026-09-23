"""Exact character/Littlewood-Richardson data and one-cross-swap witnesses.
Character computation uses Murnaghan--Nakayama on beta sets. All representation
coefficients use Python integers. LPs are discovery only unless exact-verified.
"""
from functools import lru_cache
from math import factorial, prod, gcd
from collections import Counter
from fractions import Fraction
from pathlib import Path
import json, pickle, time
import numpy as np
from scipy.optimize import linprog
ROOT=Path(__file__).resolve().parent
@lru_cache(None)
def partitions(n, cap=None):
    if n == 0: return ((),)
    if cap is None or cap>n: cap=n
    return tuple((i,)+a for i in range(cap,0,-1) for a in partitions(n-i,i))
@lru_cache(None)
def dim(a):
    n=sum(a)
    return factorial(n)//prod(a[i]-j+sum(t>j for t in a[i+1:]) for i in range(len(a)) for j in range(a[i]))
def content(a):
    return sum(v*(v-1)//2-i*v for i,v in enumerate(a))
@lru_cache(None)
def char(a,rho):
    if not rho: return int(not a)
    m=rho[0]; l=len(a); beads=[v+l-i-1 for i,v in enumerate(a)]; result=0
    for b in beads:
        new=b-m
        if new<0 or new in beads: continue
        sign=(-1)**sum(new<c<b for c in beads)
        bb=sorted([c for c in beads if c!=b]+[new],reverse=True)
        aa=tuple(c-l+i+1 for i,c in enumerate(bb) if c-l+i+1>0)
        result+=sign*char(aa,rho[1:])
    return result
@lru_cache(None)
def z(rho): return prod(k**v*factorial(v) for k,v in Counter(rho).items())
@lru_cache(None)
def table(n):
    parts=partitions(n)
    T=np.array([[char(a,r) for r in parts] for a in parts],dtype=object)
    # All character orthogonality identities, without floating point.
    w=np.array([factorial(n)//z(r) for r in parts],dtype=object)
    assert np.array_equal((T*w)@T.T, factorial(n)*np.eye(len(parts),dtype=object))
    assert all(T[i,-1]==dim(a) for i,a in enumerate(parts))
    return T

def data(n):
    file=ROOT/f'one_swap_{n}.pkl'
    if file.exists(): return pickle.loads(file.read_bytes())
    ps=partitions(n); cs=np.array([content(a) for a in ps],dtype=object)
    fs=np.array([dim(a) for a in ps],dtype=object)
    rows=[]; labels=[]; lr={}
    table(n)
    for p in range(1,n//2+1):
        q=n-p; P=partitions(p); Q=partitions(q); Tp=table(p); Tq=table(q)
        wp=np.array([factorial(p)//z(r) for r in P],dtype=object)
        wq=np.array([factorial(q)//z(r) for r in Q],dtype=object)
        coeff=np.zeros((len(P),len(Q),len(ps)),dtype=object)
        for k,nu in enumerate(ps):
            V=np.array([[char(nu,tuple(sorted(r+s,reverse=True))) for s in Q] for r in P],dtype=object)
            D=(Tp*wp)@V@(Tq*wq).T
            den=factorial(p)*factorial(q)
            assert all(int(v)%den==0 for v in D.flat)
            coeff[:,:,k]=D//den
        for i,a in enumerate(P):
            for j,b in enumerate(Q):
                if p==q and j<i: continue
                c=coeff[i,j,:]
                assert all(v>=0 for v in c)
                assert sum(c*fs)==factorial(n)//(factorial(p)*factorial(q))*dim(a)*dim(b)
                lr[(a,b)]=tuple(map(int,c))
                row=c*(cs-content(a)-content(b))
                assert sum(row*fs)==0
                if not any(row): continue
                g=0
                for v in row: g=gcd(g,abs(int(v)))
                rows.append(tuple(int(v)//g for v in row)); labels.append((a,b))
        print('n',n,'p',p,'rows',len(rows),flush=True)
    out={'n':n,'parts':ps,'dims':tuple(map(int,fs)),'rows':rows,'labels':labels,'lr':lr}
    file.write_bytes(pickle.dumps(out)); return out

def matrix(d):
    G=np.array(d['rows'],dtype=float)*np.array(d['dims'],dtype=float)
    G/=np.max(np.abs(G),axis=1)[:,None]
    return G

def feasibility(G,target):
    return linprog(np.ones(len(G)), A_eq=G.T,b_eq=target,bounds=(0,None),method='highs')

def survey(n):
    d=data(n); G=matrix(d); M=len(d['parts']); results=[]
    for j,la in enumerate(d['parts']):
        if j==0: continue
        v=np.zeros(M);v[0]=1;v[j]=-1
        r=feasibility(G,v)
        results.append((la,r.status,int(sum(r.x>1e-8)) if r.success else None))
    print('PDC feasible',sum(s==0 for _,s,_ in results),'/',M-1)
    print('PDC infeasible',[la for la,s,_ in results if s!=0])
    (ROOT/f'survey_{n}.json').write_text(json.dumps({'n':n,'generators':len(G),'pdc':results},indent=2))
    return d,G,results
if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:] or [14,15]): survey(n)
