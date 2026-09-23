"""
Reproduction script for the Groebner-basis certificates of Appendices B and D.

Part 1  verifies, in exact arithmetic, the direction that can be checked directly:
        that the claimed family annihilates the whole reduction system and the
        velocity field, and that the decisive phase relations hold on it.
Part 2  writes the ideal itself to a Singular input file, so that the elimination
        -- far too heavy for a general-purpose system -- can be rerun on exactly
        these generators in a dedicated one.

    python3 certify.py
"""
import sympy as sp, time
I = sp.I
pi = sp.pi

# ------------------------------------------------- the reduction system as modes
def reduction_modes(n):
    """(kx, sigma, coeff) for the x_1-independent part of g_1^0, phases symbolic"""
    def cyc(m): return (m - 1) % n
    Z = (0,)*(2*n)
    def unit(p, val=1, off=0):
        v = [0]*(2*n); v[off+p] = val; return tuple(v)
    def add(d, k, c):
        d[k] = d.get(k, 0) + c
        if d[k] == 0: del d[k]
    def sinf(p, q):
        d = {}; add(d, tuple(a+b for a, b in zip(unit(p), unit(q,1,n))), sp.Rational(1,2)/I)
        add(d, tuple(a+b for a, b in zip(unit(p,-1), unit(q,-1,n))), -sp.Rational(1,2)/I); return d
    def cosf(p, q):
        d = {}; add(d, tuple(a+b for a, b in zip(unit(p), unit(q,1,n))), sp.Rational(1,2))
        add(d, tuple(a+b for a, b in zip(unit(p,-1), unit(q,-1,n))), sp.Rational(1,2)); return d
    def mul(A, B):
        C = {}
        for ka, ca in A.items():
            for kb, cb in B.items(): add(C, tuple(x+y for x, y in zip(ka, kb)), ca*cb)
        return C
    def plus(*D):
        C = {}
        for d in D:
            for k, v in d.items(): add(C, k, v)
        return C
    def scal(A, c): return {k: v*c for k, v in A.items()}
    def ddx(A, p): return {k: (I*k[p])*v for k, v in A.items() if k[p] != 0}
    def T1(i):
        f = {Z: sp.Integer(1)}
        for k in range(1, n+1):
            f = mul(f, sinf(cyc(i+k-1), k-1) if k % 2 else cosf(cyc(i+k-1), k-1))
        return f
    def T2(i):
        f = sinf(cyc(i), 1)
        for k in range(2, n):
            f = mul(f, cosf(cyc(i+k-1), k) if k % 2 else sinf(cyc(i+k-1), k))
        return mul(f, cosf(cyc(i+n-1), 0))
    v = [plus(T1(i), scal(T2(i), -1)) for i in range(1, n+1)]
    g = {}
    for j in range(n):
        g = plus(g, mul(v[j], ddx(v[0], j)))
    out = {}
    for k, c in g.items():
        if k[0] != 0 and False: continue
        if k[0] == 0 and c != 0: out.setdefault(k[:n], []).append((k[n:], c))
    return out

# ------------------------------------------- part 1: the verifiable direction
def family(n):
    a = sp.Symbol('a', real=True)
    return a, ([a, a, a-pi/2, a, a-pi/2] if n == 5 else
               [a, a, a-pi/2, a, a-pi/2, a, a-pi/2])

def verify(n):
    a, xi = family(n)
    M = reduction_modes(n)
    bad = 0
    for kx, terms in M.items():
        amp = sum(c*sp.exp(I*sum(sg[t]*xi[t] for t in range(n))) for sg, c in terms)
        if sp.simplify(sp.expand(amp)) != 0: bad += 1
    print(f"  {'PASS' if bad == 0 else 'FAIL'}   n={n}: all {len(M)} amplitudes vanish "
          f"identically in a on the claimed family")
    # T1 = T2, so the field itself vanishes
    x = sp.symbols(f'x1:{n+1}', real=True)
    X = lambda m: x[(m-1) % n]
    def T1(i):
        f = sp.Integer(1)
        for k in range(1, n+1):
            arg = X(i+k-1) + xi[k-1]; f *= sp.sin(arg) if k % 2 else sp.cos(arg)
        return f
    def T2(i):
        f = sp.sin(X(i) + xi[1])
        for k in range(2, n):
            arg = X(i+k-1) + xi[k]; f *= sp.cos(arg) if k % 2 else sp.sin(arg)
        return f*sp.cos(X(i+n-1) + xi[0])
    ok = all(sp.simplify(sp.expand_trig(T1(i) - T2(i))) == 0 for i in range(1, n+1))
    print(f"  {'PASS' if ok else 'FAIL'}   n={n}: T1 = T2 on the family, so v^0 = 0 identically")
    same  = [1, 3] if n == 5 else [1, 3, 5]
    quart = [2, 4] if n == 5 else [2, 4, 6]
    rel = (all(sp.simplify(sp.cos(2*(xi[0]-xi[k])) - 1) == 0 for k in same) and
           all(sp.simplify(sp.cos(2*(xi[0]-xi[k])) + 1) == 0 for k in quart))
    print(f"  {'PASS' if rel else 'FAIL'}   n={n}: the decisive phase relations hold on the family")


# ------------------------------------------- part 2: Singular input generation
def write_singular(n, path):
    """write the ideal to a Singular script, so the elimination can be rerun
       on the same generators in a system able to complete it"""
    M = reduction_modes(n)
    s = sp.symbols(f's1:{n+1}', real=True); c = sp.symbols(f'c1:{n+1}', real=True)
    def expo(sig):
        e = sp.Integer(1)
        for i, m in enumerate(sig):
            if m == 0: continue
            h = m//2; z = c[i] + I*s[i]
            e *= z**h if h > 0 else (c[i] - I*s[i])**(-h)
        return e
    gens = []
    for kx, terms in M.items():
        amp = sp.expand(sum(co*expo(sg) for sg, co in terms))
        re, im = amp.as_real_imag()
        for p in (sp.expand(re), sp.expand(im)):
            if p != 0: gens.append(p)
    with open(path, 'w') as f:
        f.write(f"// Groebner-basis reduction of the {n}-dimensional phase system.\n")
        f.write(f"// Generated by certify.py; see Appendix {'B' if n == 5 else 'D'}.\n")
        f.write("ring R = 0,(" + ",".join(f"s{i+1},c{i+1}" for i in range(n)) + "),dp;\n")
        allg = [str(p).replace("**", "^") for p in gens] + \
               [f"s{i+1}^2+c{i+1}^2-1" for i in range(n)]
        f.write("ideal I =\n  " + ",\n  ".join(allg) + ";\n")
        f.write("option(redSB);\nideal G = groebner(I);\n")
        f.write('"basis size:"; size(G);\n"Krull dimension:"; dim(G);\n')
        f.write("poly R1 = c1*c2+s1*s2-1;    // xi_2 = xi_1 (mod pi)\n")
        f.write('"reduce(R1^2,G) ="; reduce(R1^2,G);   // expect 0\n')
    print(f"  wrote {path}: {len(gens)} amplitude generators + {n} Pythagorean "
          f"relations in {2*n} variables")

if __name__ == "__main__":
    print("Certificate reproduction for Appendices B and D.")
    print(f"SymPy {sp.__version__}\n")
    print("Part 1 -- the verifiable direction (exact, self-contained):")
    for n in (5, 7):
        t = time.time(); verify(n); print(f"          ({time.time()-t:.1f} s)")
    print("\nPart 2 -- generating Singular input for the elimination:")
    for n, p in ((5, "reduction_5D.sing"), (7, "reduction_7D.sing")):
        t = time.time(); write_singular(n, p); print(f"          ({time.time()-t:.1f} s)")

