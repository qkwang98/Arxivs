#!/usr/bin/env python3
"""Exact checks independent of the LP and of the skew-tableau coefficient code.
1. Direct symmetric-group character sums reproduce small-order witness traces.
2. A complex, singular rank-13, two-connected fan of PSD triangles tests every
   delivered witness on a nontrivial exact Gram geometry. These are checks,
   not substitutes for the arbitrary-PSD proof.
"""
from verify_certificate import *
from collections import defaultdict
from itertools import permutations
from math import prod
import time

@lru_cache(None)
def mn(shape,cycle):
    if not cycle:return int(not shape)
    k=cycle[0];ans=0
    for small in partitions(sum(shape)-k):
        if not contains(shape,small):continue
        boxes={(i,j) for i,row in enumerate(shape)
               for j in range(small[i] if i<len(small) else 0,row)}
        if len(boxes)!=k:continue
        if any((i+1,j) in boxes and (i,j+1) in boxes and (i+1,j+1) in boxes for i,j in boxes):continue
        seen={next(iter(boxes))}
        while True:
            more=seen|{p for i,j in seen for p in ((i+1,j),(i-1,j),(i,j+1),(i,j-1)) if p in boxes}
            if more==seen:break
            seen=more
        if seen==boxes:
            ans+=(-1)**(len({i for i,j in boxes})-1)*mn(small,cycle[1:])
    return ans

def ctype(p):
    seen=set();out=[]
    for i in range(len(p)):
        if i in seen:continue
        j=i;k=0
        while j not in seen:seen.add(j);k+=1;j=p[j]
        out.append(k)
    return tuple(sorted(out,reverse=True))

def compose(a,b):return tuple(a[b[i]] for i in range(len(a)))

def direct_small(n,k):
    """Trace in V_nu of P_mu P_beta tau P_eta by literal group-algebra sums."""
    b=n-k;a=n-2*k
    tau=list(range(n))
    for i in range(k):tau[a+i],tau[b+i]=tau[b+i],tau[a+i]
    tau=tuple(tau)
    gleft=list(permutations(range(b)))
    gearly=list(permutations(range(a)))
    betas=[1] if k==1 else [1,-1]
    right=list(permutations(range(k)))
    total=0
    for eta in partitions(a):
      for mu in partitions(b):
       for sign in betas:
        sums=defaultdict(F)
        for sigma0 in gleft:
          c1=F(degree(mu),factorial(b))*mn(mu,ctype(sigma0))
          if not c1:continue
          sigma=sigma0+tuple(range(b,n))
          for gam0 in gearly:
            c2=F(degree(eta),factorial(a))*mn(eta,ctype(gam0))
            if not c2:continue
            gam=gam0+tuple(range(a,n))
            for beta0 in right:
              char=1 if k==1 or beta0==(0,1) else sign
              beta=tuple(range(b))+tuple(b+i for i in beta0)
              typ=ctype(compose(compose(compose(sigma,beta),tau),gam))
              sums[typ]+=c1*c2*F(char,factorial(k))
        computed={nu:sum(c*mn(nu,typ) for typ,c in sums.items())/degree(eta) for nu in partitions(n)}
        computed={p:c for p,c in computed.items() if c}
        expected=witness_coefficients(k,eta,mu,sign)
        assert computed==expected,(n,k,eta,mu,sign,computed,expected)
        total+=1
    print('PASS literal character-sum check: n=%d,k=%d, witnesses=%d'%(n,k,total))

# Gaussian-integer arithmetic.
def gaussadd(a,b):return a[0]+b[0],a[1]+b[1]
def gaussmul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]

def fan_matrix(n=14):
    # Each 3x3 block has eigenvalues 0, 3-sqrt(3), 3+sqrt(3).
    # Its kernel is the constants. The connected overlapping fan therefore
    # has exactly the all-ones kernel and rank n-1.
    A=[[(0,0) for _ in range(n)] for _ in range(n)]
    for i in range(1,n-1):
        tri=(0,i,i+1)
        for j in tri:A[j][j]=gaussadd(A[j][j],(2,0))
        for j in range(3):
            u,v=tri[j],tri[(j+1)%3]
            A[u][v]=gaussadd(A[u][v],(-1,1))
            A[v][u]=gaussadd(A[v][u],(-1,-1))
    assert all(tuple(sum(A[i][j][k] for j in range(n)) for k in range(2))==(0,0) for i in range(n))
    return A

def class_monomials(A):
    n=len(A);rows=sorted(range(n),key=lambda i:sum(x!=(0,0) for x in A[i]))
    choices={i:[j for j in range(n) if A[i][j]!=(0,0)] for i in range(n)}
    vals=defaultdict(lambda:(0,0));sigma=[-1]*n;count=0
    def dfs(k,used,weight):
        nonlocal count
        if k==n:
            typ=ctype(tuple(sigma));vals[typ]=gaussadd(vals[typ],weight);count+=1;return
        i=rows[k]
        for j in choices[i]:
            if not (used>>j)&1:
                sigma[i]=j;dfs(k+1,used|(1<<j),gaussmul(weight,A[i][j]))
    dfs(0,0,(1,0))
    assert all(v[1]==0 for v in vals.values())
    print('Exact fan: supported permutations',count,'conjugacy types',len(vals))
    return {t:v[0] for t,v in vals.items()}

def exact_fan_check():
    data=json.loads(Path(__file__).with_name('certificate.json').read_text())
    A=fan_matrix();vals=class_monomials(A)
    ds={p:sum(mn(p,t)*v for t,v in vals.items()) for p in partitions(14)}
    assert all(v>=0 for v in ds.values())
    slacks=[]
    for i,r in enumerate(data['rows'],1):
        row=parse_row(r['coefficients']);slack=sum(c*ds[p] for p,c in row.items())
        assert slack>=0,('negative witness',i,slack)
        slacks.append(str(slack))
    pp=ds[(14,)];dd=ds[(4,4,3,3)]
    rhs=sum(c*ds[p] for p,c in parse_row(data['identity']).items())
    assert rhs==sum(F(r['weight'])*F(s) for r,s in zip(data['rows'],slacks))
    assert dd<12012*pp
    output={'rank':'13 (analytically certified)','permanent':str(pp),'target_immanant':str(dd),
            'bridge_slack':str(rhs),'witness_slacks':slacks}
    Path(__file__).with_name('adversarial_fan_output.json').write_text(json.dumps(output,indent=2))
    print('PASS all 20 witnesses on exact complex rank-13 fan; bridge slack',rhs)

if __name__=='__main__':
    direct_small(4,1);direct_small(4,2);direct_small(5,2);direct_small(6,2)
    exact_fan_check()
