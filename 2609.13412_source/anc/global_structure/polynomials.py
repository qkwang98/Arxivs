"""Small exact sparse polynomial ring; Python standard library only.

All polynomials have three indeterminates. Coefficients are fractions.
This file contains no numerical optimization or floating-point arithmetic.
"""
from fractions import Fraction as F
from math import comb

class P:
    def __init__(self, terms=0):
        if isinstance(terms, P): terms=terms.d
        if not isinstance(terms, dict):terms={(0,0,0):F(terms)}
        self.d={tuple(k):F(v) for k,v in terms.items() if v}
    @staticmethod
    def var(i):
        e=[0,0,0];e[i]=1;return P({tuple(e):1})
    def __add__(self,other):
        other=P(other);out=dict(self.d)
        for e,v in other.d.items():out[e]=out.get(e,F(0))+v
        return P(out)
    __radd__=__add__
    def __neg__(self):return P({e:-v for e,v in self.d.items()})
    def __sub__(self,other):return self+-P(other)
    def __rsub__(self,other):return P(other)+-self
    def __mul__(self,other):
        other=P(other);out={}
        for e,v in self.d.items():
            for f,w in other.d.items():
                k=tuple(a+b for a,b in zip(e,f));out[k]=out.get(k,F(0))+v*w
        return P(out)
    __rmul__=__mul__
    def __truediv__(self,c):return self*F(1,c)
    def __pow__(self,n):
        if n<0:raise ValueError('Nonnegative powers only')
        ans=P(1);base=self
        while n:
            if n&1:ans=ans*base
            base=base*base;n//=2
        return ans
    def coeff(self,i,k):
        out={}
        for e,v in self.d.items():
            if e[i]==k:
                f=list(e);f[i]=0;out[tuple(f)]=v
        return P(out)
    def degree(self,i):return max((e[i] for e in self.d),default=0)
    def subst(self,i,value):
        value=P(value);ans=P(0)
        for k in range(self.degree(i)+1):ans=ans+self.coeff(i,k)*value**k
        return ans
    def value(self,*xs):
        return sum((v*F(xs[0])**e[0]*F(xs[1])**e[1]*F(xs[2])**e[2] for e,v in self.d.items()),F(0))
    def nonnegative_coefficients(self):return all(v>=0 for v in self.d.values())
    def to_json(self):return [[list(e),str(v)] for e,v in sorted(self.d.items())]
    def __eq__(self,other):return self.d==P(other).d

def powers(a,l):
    """Sums of the first three powers of a,a+1,...,a+l-1."""
    a=P(a);l=P(l)
    s1=l*a+l*(l-1)/2
    s2=l*a*a+a*l*(l-1)+l*(l-1)*(2*l-1)/6
    s3=l*a**3+3*a*a*l*(l-1)/2+a*l*(l-1)*(2*l-1)/2+l*l*(l-1)*(l-1)/4
    return s1,s2,s3

def elementary(ps):
    p1,p2,p3=ps
    return p1,(p1*p1-p2)/2,(p1**3-3*p1*p2+2*p3)/6

def kappa(rows):return sum((P(x)*(P(x)+1-2*i)/2 for i,x in enumerate(rows,1)),P(0))

def family_DE(a,b,g,c):
    a,b,g=P(a),P(b),P(g)
    h=b-g-c
    ps1=powers(a,h);ps2=powers(2,g)
    ps=[ps1[k-1]+ps2[k-1]+sum((-3+j)**k for j in range(c)) for k in (1,2,3)]
    e1,e2,e3=elementary(ps)
    o1,o2,o3=elementary(powers(0,b))
    n1=e1-o1;n2=e2-o2-o1*n1
    D=e3-o3-o2*n1-(o1-1)*n2
    E=kappa((a+b-g-c,g+3,3,c))-kappa((b,3,3))-a*(a-1)/2
    return D,E

def family_H(a,b,g,c):
    a,b,g=P(a),P(b),P(g)
    D,E=family_DE(a,b,g,c)
    return (2*b+4-a)*D+b*(b+1)*(3*a-4*b+4)*E

def bernstein_coefficients(poly):
    if poly.degree(2)>4:raise ArithmeticError('Degree exceeds four')
    return [sum((poly.coeff(2,i)*F(comb(k,i),comb(4,i)) for i in range(k+1)),P(0)) for k in range(5)]

def global_bernstein(c):
    g,u,x=[P.var(i) for i in range(3)]
    b=g+u+(5 if c==3 else 3)
    a=8*b/5+(2*b/5+4)*x
    return bernstein_coefficients(family_H(a,b,g,c))
