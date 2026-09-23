#!/usr/bin/env python3
"""Exact 4-qubit check of the partial-transpose sandwich and complex-product
expectation identities. Standard library only, Gaussian rational arithmetic.
This finite test is supplementary; the universal proof is in PROOF.md.
"""
from fractions import Fraction as F
from itertools import product

Z=(F(0),F(0)); ONE=(F(1),F(0))
def z(x,y=0):return (F(x),F(y))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def bar(a):return (a[0],-a[1])
def scale(a,t):return (a[0]*t,a[1]*t)
def zsum(xs):
    a=Z
    for x in xs:a=add(a,x)
    return a

def mm(A,B):
    n=len(A);m=len(B);p=len(B[0])
    return [[zsum(mul(A[i][k],B[k][j]) for k in range(m)) for j in range(p)] for i in range(n)]
def mv(A,v):return [zsum(mul(a,b) for a,b in zip(row,v)) for row in A]
def outer(v):return [[mul(a,bar(b)) for b in v] for a in v]
def quadratic(v,A):return zsum(mul(bar(a),b) for a,b in zip(v,mv(A,v)))
def kron(A,B):return [[mul(a,b) for a in rowA for b in rowB] for rowA in A for rowB in B]
def tensor(vs):
    out=[ONE]
    for v in vs:out=[mul(a,b) for a in out for b in v]
    return out

def partial_transpose(A,left=4,right=4):
    # (a,b ; c,d) -> (a,d ; c,b), transpose the whole right subsystem.
    return [[A[(i//right)*right+j%right][(j//right)*right+i%right]
             for j in range(left*right)] for i in range(left*right)]

def main():
    # Two qubits on each side. tau swaps the two 4-dimensional sides.
    swap=[[ONE if i//4==j%4 and i%4==j//4 else Z for j in range(16)] for i in range(16)]
    E=partial_transpose(swap)
    omega=[ONE if i//4==i%4 else Z for i in range(16)]
    assert E==outer(omega)
    # A genuinely complex rank-one Hermitian projector on the first side.
    a=[z(1),z(0,1),z(1),z(0,-1)]
    C=[[scale(x,F(1,4)) for x in row] for row in outer(a)]
    assert mm(C,C)==C
    local_swap=[[ONE if (i//2,i%2)==(j%2,j//2) else Z for j in range(4)] for i in range(4)]
    vs=[[z(1),z(2,1)],[z(1,-1),z(3)],[z(2),z(-1,2)],[z(1,1),z(2,-1)]]
    v=tensor(vs);vbar=tensor(vs[:2]+[[bar(a) for a in t] for t in vs[2:]])
    for sign in (1,-1):
        B=[[scale(add(ONE if i==j else Z,scale(local_swap[i][j],sign)),F(1,2)) for j in range(4)] for i in range(4)]
        assert mm(B,B)==B
        K=kron(C,B)
        Y=mm(mm(K,E),K)
        W=mm(mm(K,swap),K)
        assert Y==outer(mv(K,omega)) # exact PSD factorization
        assert partial_transpose(Y)==W
        lhs=quadratic(v,W);rhs=quadratic(vbar,Y)
        assert lhs==rhs and lhs[1]==0 and lhs[0]>=0
        print('PASS exact operator sandwich and complex product expectation, sign',sign,'value',lhs[0])

if __name__=='__main__':main()
