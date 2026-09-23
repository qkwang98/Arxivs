import sympy as sp
pi = sp.pi

def field(n, xi, alpha=1):
    x = sp.symbols(f'x1:{n+1}', real=True)
    X = lambda m: x[(m - 1) % n]
    def T1(i):
        f = sp.Integer(1)
        for k in range(1, n + 1):
            arg = alpha * X(i + k - 1) + xi[k - 1]
            f *= sp.sin(arg) if k % 2 else sp.cos(arg)
        return f
    def T2(i):
        f = sp.sin(alpha * X(i) + xi[1])
        for k in range(2, n):
            arg = alpha * X(i + k - 1) + xi[k]
            f *= sp.cos(arg) if k % 2 else sp.sin(arg)
        return f * sp.cos(alpha * X(i + n - 1) + xi[0])
    return x, [T1(i) for i in range(1, n+1)], [T2(i) for i in range(1, n+1)]

def velocity(n, xi):
    x, T1, T2 = field(n, xi)
    return x, [sp.expand_trig(sp.expand(T1[i] - T2[i])) for i in range(n)]

def convective(n, xi):
    x, v = velocity(n, xi)
    return x, [sp.expand(sum(v[j]*sp.diff(v[i], x[j]) for j in range(n)))
               for i in range(n)]

def reduction_term(n, xi):
    from sympy.simplify.fu import TR8
    x, g = convective(n, xi)
    e = sp.expand(TR8(sp.expand(g[0])))
    return sp.simplify(sum(t for t in sp.Add.make_args(e) if not t.has(x[0])))

def integrability_defect(n, xi):
    from sympy.simplify.fu import TR8
    x, g = convective(n, xi)
    worst = sp.Integer(0)
    for i in range(n):
        for j in range(i+1, n):
            dd = sp.diff(g[i], x[j]) - sp.diff(g[j], x[i])
            d = sp.simplify(TR8(sp.expand(dd)))
            if d != 0: worst = d
    return worst

def check(label, ok):
    print(f"  {'PASS' if ok else 'FAIL'}   {label}")

fam1 = lambda t, l1, l2: [t, t - 2*pi/3 + l1*pi, t + pi/6 + l2*pi]
fam2 = lambda t, l1, l2: [t, t + 2*pi/3 + l1*pi, t + 5*pi/6 + l2*pi]

def three_dimensions():
    print("\nTHREE DIMENSIONS")
    for name, xi in (("first  family", fam1(pi/8, 0, 0)),
                     ("second family", fam2(-pi/3, 0, 0))):
        ok = (reduction_term(3, xi) == 0 and integrability_defect(3, xi) == 0
              and any(sp.simplify(c) != 0 for c in velocity(3, xi)[1]))
        check(f"{name}: xi = {[sp.nsimplify(u) for u in xi]}", ok)
    va = velocity(3, fam1(pi/8, 0, 0))[1]
    vb = velocity(3, fam1(pi/8, 1, 0))[1]
    check("adding pi to one phase reverses v^0",
          all(sp.simplify(sp.expand_trig(va[i] + vb[i])) == 0 for i in range(3)))

def four_dimensions():
    print("\nFOUR DIMENSIONS")
    curve = lambda t, a: [t, t + a, t + pi/2, t + a]
    for a in (pi/2, pi/3, sp.Rational(3,10)*pi):
        red = reduction_term(4, curve(0, a)) == 0
        itg = integrability_defect(4, curve(0, a)) == 0
        check(f"a = {sp.nsimplify(a)}: reduction holds, integrability "
              f"{'holds' if itg else 'fails'}", red)
    xi = curve(-pi/4, pi/2)
    check("known 4D solution (-pi/4,pi/4,pi/4,pi/4) satisfies both",
          reduction_term(4, xi) == 0 and integrability_defect(4, xi) == 0)

def five_dimensions():
    print("\nFIVE DIMENSIONS")
    a = sp.Symbol('a', real=True)
    xi = [a, a, a - pi/2, a, a - pi/2]
    check("family (5.6) satisfies the reduction condition",
          reduction_term(5, xi) == 0)
    x, T1, T2 = field(5, xi)
    check("family (5.6) gives T1 = T2, so v^0 = 0 identically",
          all(sp.simplify(sp.expand_trig(T1[i] - T2[i])) == 0 for i in range(5)))
    xj = [sp.Integer(0), sp.Rational(1,5), -pi/2, sp.Integer(0), -pi/2]
    check("a nearby non-member fails the reduction condition",
          reduction_term(5, xj) != 0)

def curl_pair(n, xi, i, j):
    """dg_i/dx_j - dg_j/dx_i  for 0-based i, j"""
    from sympy.simplify.fu import TR8
    x, v = velocity(n, xi)
    g = [sp.expand(sum(v[b]*sp.diff(v[a], x[b]) for b in range(n)))
         for a in range(n)]
    return sp.simplify(TR8(sp.expand(sp.diff(g[i], x[j]) - sp.diff(g[j], x[i]))))

def even_dimension(n):
    """the dichotomy of Theorem 6.7, at the symmetric phases"""
    xi = [-pi/4] + [pi/4]*(n - 1)
    red  = reduction_term(n, xi) == 0
    triv = all(sp.simplify(c) == 0 for c in velocity(n, xi)[1])
    ev   = curl_pair(n, xi, 0, 2) == 0        # even offset
    od   = curl_pair(n, xi, 0, 1) == 0        # odd offset
    print(f"\n{n} DIMENSIONS (symmetric phases)")
    print(f"   reduction condition (3.12) : {'holds' if red else 'FAILS'}")
    kind = 'trivial' if triv else 'non-trivial'
    print(f"   velocity field             : {kind}")
    print(f"   integrability, pair (1,3)  : {'holds' if ev else 'fails'}"
          "   [even offset]")
    print(f"   integrability, pair (1,2)  : {'holds' if od else 'fails'}"
          "   [odd offset]")
    print("   => curl-free throughout; unforced solution exists."
          if ev and od else
          "   => curl-free on even offsets only; no pressure exists.")

# --- Proposition 4.1: the 3D classification, by Groebner basis ---
def classification_3D():
    ca, sa, cb, sb = sp.symbols('c_a s_a c_b s_b')
    cosAB  = ca*cb - sa*sb
    sinAB  = sa*cb + ca*sb
    cos2AB = (2*ca**2 - 1)*cb - 2*sa*ca*sb
    sin2AB = 2*sa*ca*cb + (2*ca**2 - 1)*sb
    p1 = sp.expand(-1 - ca - cos2AB - 2*cb + cosAB)
    p2 = sp.expand(-sa - sin2AB + sinAB)
    G  = sp.groebner([p1, p2, ca**2+sa**2-1, cb**2+sb**2-1],
                     ca, sa, cb, sb, order='lex')
    elim = sp.factor(G.exprs[-1])
    print("\nTHREE-DIMENSIONAL CLASSIFICATION (Proposition 4.1)")
    print(f"   zero-dimensional ideal      : {G.is_zero_dimensional}")
    print(f"   elimination polynomial (4.9): {elim}")

import math, cmath

def _modes(n, xi):
    """v_i^0 and g_i^0 as Fourier dicts at numeric phases (alpha=v_r=1)"""
    def cyc(m): return (m-1)%n
    Z=(0,)*n
    def unit(p,v=1):
        z=[0]*n; z[p]=v; return tuple(z)
    def add(d,k,c):
        d[k]=d.get(k,0)+c
        if abs(d[k])<1e-13: d.pop(k,None)
    def sinf(p,ph):
        d={}; add(d, unit(p), cmath.exp(1j*ph)/2j)
        add(d, unit(p,-1), -cmath.exp(-1j*ph)/2j); return d
    def cosf(p,ph):
        d={}; add(d, unit(p), cmath.exp(1j*ph)/2)
        add(d, unit(p,-1), cmath.exp(-1j*ph)/2); return d
    def mul(A,B):
        C={}
        for ka,ca in A.items():
            for kb,cb in B.items():
                add(C,tuple(x+y for x,y in zip(ka,kb)),ca*cb)
        return C
    def plus(*D):
        C={}
        for d in D:
            for k,v in d.items(): add(C,k,v)
        return C
    def scal(A,c): return {k:v*c for k,v in A.items()}
    def ddx(A,p): return {k:(1j*k[p])*v for k,v in A.items() if k[p]!=0}
    def T1(i):
        f={Z:1+0j}
        for k in range(1,n+1):
            q=cyc(i+k-1); ph=xi[k-1]
            f=mul(f, sinf(q,ph) if k%2 else cosf(q,ph))
        return f
    def T2(i):
        f=sinf(cyc(i),xi[1])
        for k in range(2,n):
            f=mul(f, cosf(cyc(i+k-1),xi[k]) if k%2 else sinf(cyc(i+k-1),xi[k]))
        return mul(f, cosf(cyc(i+n-1),xi[0]))
    v=[plus(T1(i),scal(T2(i),-1)) for i in range(1,n+1)]
    g=[]
    for i in range(n):
        acc={}
        for j in range(n): acc=plus(acc, mul(v[j], ddx(v[i],j)))
        g.append(acc)
    return v,g

def helmholtz_character(n, xi):
    v,g=_modes(n,xi)
    div={}
    for i in range(n):
        for k,c in g[i].items(): div[k]=div.get(k,0)+1j*k[i]*c
    dv=max([abs(c) for c in div.values()]+[0.0])
    cu=0.0
    for i in range(n):
        for j in range(i+1,n):
            for k in set(g[i])|set(g[j]):
                cu=max(cu,abs(1j*k[j]*g[i].get(k,0)-1j*k[i]*g[j].get(k,0)))
    modes=sum(len(v[i]) for i in range(n))
    if cu<1e-12: return "longitudinal (pure gradient)", dv, cu, modes
    if dv<1e-12: return "transverse (divergence-free)", dv, cu, modes
    return "both parts present", dv, cu, modes

def helicity(xi):
    """int v.curl(v) over the cell, n=3"""
    v,_=_modes(3,xi)
    w=[{},{},{}]
    def add(d,k,c): d[k]=d.get(k,0)+c
    for k,c in v[2].items(): add(w[0],k, 1j*k[1]*c)
    for k,c in v[1].items(): add(w[0],k,-1j*k[2]*c)
    for k,c in v[0].items(): add(w[1],k, 1j*k[2]*c)
    for k,c in v[2].items(): add(w[1],k,-1j*k[0]*c)
    for k,c in v[1].items(): add(w[2],k, 1j*k[0]*c)
    for k,c in v[0].items(): add(w[2],k,-1j*k[1]*c)
    tot=0
    for i in range(3):
        for k,c in v[i].items():
            kn=tuple(-t for t in k)
            if kn in w[i]: tot+=c*w[i][kn]
    return (tot*(2*math.pi)**3).real

if __name__ == "__main__":
    import math
    print("Verification of the results reported in the paper.")
    print(f"SymPy {sp.__version__}")
    three_dimensions()
    classification_3D()
    four_dimensions()
    five_dimensions()
    even_dimension(4)
    even_dimension(6)
    pi_ = math.pi
    print("\nHELMHOLTZ CHARACTER OF g^0 (Table 2)")
    for n, xi in ((3, [pi_/8, -13*pi_/24, 7*pi_/24]), (4, [-pi_/4]+[pi_/4]*3),
                  (5, [-pi_/4]+[pi_/4]*4), (6, [-pi_/4]+[pi_/4]*5),
                  (7, [-pi_/4]+[pi_/4]*6), (8, [-pi_/4]+[pi_/4]*7)):
        ch, dv, cu, m = helmholtz_character(n, xi)
        print(f"   n={n}: {ch:30s} |div|={dv:.1e}  |curl|={cu:.1e}")
    print("\nHELICITY OF THE TWO THREE-DIMENSIONAL FAMILIES (4.13)")
    for nm, xi in (("first  family", [pi_/8, -13*pi_/24, 7*pi_/24]),
                   ("second family", [-pi_/3, pi_/3, pi_/2])):
        print(f"   {nm}: H = {helicity(xi):+.6f}"
              f"   (27*sqrt(3)*pi^3/4 = {27*math.sqrt(3)*pi_**3/4:.6f})")
    print("\nDone.")
