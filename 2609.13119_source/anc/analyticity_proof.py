from sage.all import QQ, matrix
from sage.algebras.weyl_algebra import DifferentialWeylAlgebra, PolynomialRing

from itertools import combinations_with_replacement

################################ §1 Coordinates ##########################################
#
# We work with natural coordinates on sl_2(R) x R^2 x R_2
#
# (y11  y12 v1)
# (y21 -y11 v2)
# (w1   w2    )
#
# The following is the corresponding Weyl algebra

Wy = DifferentialWeylAlgebra(QQ, names=('y11', 'y12', 'y21', 'v1', 'v2', 'w1', 'w2'))
Ry = Wy.polynomial_ring()

y_vars = Ry.gens()
y_pars = Wy.differentials()

y11, y12, y21, v1, v2, w1, w2 = y_vars
dy11, dy12, dy21, dv1, dv2, dw1, dw2 = y_pars

# GL_2(R) acts on gl_3(R) by conjugation
#
# Let X \in gl_2(R) and Φ a smooth function on gl_3(R)
#
# Our convention is (X.Φ)(Y) = (d/dt)Φ(exp(-tX).Y) at t = 0
#
# For the standard basis E11, E12, E21, E22 of gl_2(R) this gives

E11 = -y12*dy12 - v1*dv1 + y21*dy21 + w1*dw1
E22 = -y21*dy21 - v2*dv2 + y12*dy12 + w2*dw2
E12 = -y21*dy11 + 2*y11*dy12 - v2*dv1 + w1*dw2
E21 =  y12*dy11 - 2*y11*dy21 - v1*dv2 + w2*dw1

# The following defines the subring of invariant functions and its Weyl algebra

Wabc = DifferentialWeylAlgebra(QQ, names=('a', 'b', 'c'))
Rabc = Wabc.polynomial_ring()

abc_vars = Rabc.gens()
abc_pars = Wabc.differentials()

a, b, c = abc_vars
da, db, dc = abc_pars

rho = {a : -y11**2 - y12*y21, b : v1*w1 + v2*w2, c : w1*(y11*v1 + y12*v2) + w2*(y21*v1 - y11*v2)}

############################# §2 Invariant differentials #################################
#
# Recall that sl_2(R) x R^2 x R_2 \subset gl_3(R)
#
# φ = exp(tr(Y Y^t)/2) is our Gaussian where Y \in gl_3(R)
#
# This convention differs from the one in the paper by scaling all variables by 2\sqrt{π} which does not affect the proof of analyticity of Orb(-, (y12 - y21).φ)
#
# The advantage of the scaling is that there will be no powers of π in the ensuing formulas which makes them much more readable

def apply_to_Gaussian(D, f):
    """
    D is a differential operator on sl_2(R) x R^2 x R_2
    f is a polynomial on sl_2(R) x R^2 x R_2

    result is the polynomial g such that D(f.φ) = g.φ
    """
    res = Wy.zero()
    for (v, p), coeff in D.monomial_coefficients().items():
        res += coeff * y11**v[0] * y12**v[1] * y21**v[2] * v1**v[3] * v2**v[4] * w1**v[5] * w2**v[6] * (dy11 - 2*y11)**p[0] * (dy12 - y12)**p[1] * (dy21 - y21)**p[2] * (dv1 - v1)**p[3] * (dv2 - v2)**p[4] * (dw1 - w1)**p[5] * (dw2 - w2)**p[6]
    return res.diff(f)

print()
print('We define four tuples of the form (D, f11, f12, f21, f22, D_abc) where\n\n - D is a GL_2-invariant differential operator on sl_2(R) x R^2 x R_2\n - fij is a polynomial function on sl_2(R) x R^2 x R_2\n - D((y12 - y21).φ) + E11(f11.φ) + E12(f12.φ) + E21(f21.φ) + E22(f22.φ) = 0\n - D_abc is the restriction of D to C[a, b, c]\n\n --> In particular, D_abc annihilates Orb(-, (y12 - y21).φ)')

D = 4*dy12*dy21 + dy11**2 - 4*y12*y21 - 4*y11**2 - 2
order_D = 2
f11 = 0
f12 = 0
f21 = 0
f22 = 0
D_abc = b**2*dc**2 - 4*c*da*dc - 4*a*da**2 - 6*da + 4*a - 2
tup1 = (D, f11, f12, f21, f22, D_abc, order_D)

D = -dv2*dw2 - dv1*dw1 + v2*w2 + v1*w1
order_D = 2
f11 = 0
f12 = 0
f21 = 0
f22 = 0
D_abc = a*b*dc**2 - 2*c*db*dc - b*db**2 - 2*db + b
tup2 = (D, f11, f12, f21, f22, D_abc, order_D)

D = -2*y21*v1*dv2**2*dw2 + 2*y11*v2*dv2**2*dw2 - 2*y12*v2*dv1*dv2*dw2 - 2*y11*v1*dv1*dv2*dw2 - 2*y21*v1*dv1*dv2*dw1 + 2*y11*v2*dv1*dv2*dw1 - 2*y12*v2*dv1**2*dw1 - 2*y11*v1*dv1**2*dw1 - 2*y11*y21*dy21*dv2*dw2 + 2*y21**2*dy21*dv2*dw1 - 2*y12*y21*dy21*dv1*dw2 - 4*y11**2*dy21*dv1*dw2 + 2*y11*y21*dy21*dv1*dw1 - 2*y11*y12*dy12*dv2*dw2 - 2*y12*y21*dy12*dv2*dw1 - 4*y11**2*dy12*dv2*dw1 + 2*y12**2*dy12*dv1*dw2 + 2*y11*y12*dy12*dv1*dw1 + 2*y12*y21*dy11*dv2*dw2 + 2*y11*y21*dy11*dv2*dw1 + 2*y11*y12*dy11*dv1*dw2 - 2*y12*y21*dy11*dv1*dw1 - 4*y11*dv2*dw2 + 4*y21*dv2*dw1 + 4*y12*dv1*dw2 + 4*y11*dv1*dw1 - 2*v2**2*w2*dy21*dv1 - 2*v1*v2*w1*dy21*dv1 + 2*y21*v2*w1*dy21**2 - 2*v1*v2*w2*dy12*dv2 - 2*v1**2*w1*dy12*dv2 - 2*y21*v1*w2*dy12*dy21 - 2*y12*v2*w1*dy12*dy21 + 4*y11*v2*w2*dy12*dy21 - 4*y11*v1*w1*dy12*dy21 + 2*y12*v1*w2*dy12**2 + v2**2*w2*dy11*dv2 + v1*v2*w1*dy11*dv2 - v1*v2*w2*dy11*dv1 - v1**2*w1*dy11*dv1 - y21*v2*w2*dy11*dy21 + y21*v1*w1*dy11*dy21 + 2*y11*v2*w1*dy11*dy21 - y12*v2*w2*dy11*dy12 + y12*v1*w1*dy11*dy12 + 2*y11*v1*w2*dy11*dy12 - y21*v1*w2*dy11**2 - y12*v2*w1*dy11**2 + 2*y21*v1*w2 + 2*y12*v2*w1 - 2*y11*v2*w2 + 2*y11*v1*w1

order_D = 3

f11 = 0
f12 = 0
f21 = 0
f22 = 0
D_abc = 2*a*c**2*dc**3 + 6*a*b*c*db*dc**2 + 4*a*b**2*db**2*dc - 2*c**2*db**2*dc - 2*b*c*db**3 - b**2*c*dc**2 + 6*a*c*dc**2 - b**3*db*dc + 8*a*b*db*dc - 2*c*db**2 + 2*c**2*da*dc + 2*b*c*da*db - 3*b**2*dc + 4*c*da + 2*c
tup3 = (D, f11, f12, f21, f22, D_abc, order_D)

D = 2*y12*y21*v2*dv2**2*dw2 + 2*y11*y21*v1*dv2**2*dw2 - 2*y21**2*v1*dv2**2*dw1 + 2*y11*y21*v2*dv2**2*dw1 + 4*y11*y12*v2*dv1*dv2*dw2 + 4*y11**2*v1*dv1*dv2*dw2 - 4*y11*y21*v1*dv1*dv2*dw1 + 4*y11**2*v2*dv1*dv2*dw1 - 2*y12**2*v2*dv1**2*dw2 - 2*y11*y12*v1*dv1**2*dw2 + 2*y12*y21*v1*dv1**2*dw1 - 2*y11*y12*v2*dv1**2*dw1 + 2*v2**2*w1*dy21**2*dv1 - 2*v2**2*w2*dy12*dy21*dv2 - 2*v1**2*w1*dy12*dy21*dv1 + 2*v1**2*w2*dy12**2*dv2 - v2**2*w1*dy11*dy21*dv2 - v2**2*w2*dy11*dy21*dv1 + 2*v1*v2*w1*dy11*dy21*dv1 - 2*v1*v2*w2*dy11*dy12*dv2 + v1**2*w1*dy11*dy12*dv2 + v1**2*w2*dy11*dy12*dv1 - v1*v2*w1*dy11**2*dv2 - v1*v2*w2*dy11**2*dv1 + 4*y12*y21*dv2*dw2 + 4*y11**2*dv2*dw2 + 4*y12*y21*dv1*dw1 + 4*y11**2*dv1*dw1 - 4*v2*w2*dy12*dy21 - 4*v1*w1*dy12*dy21 - v2*w2*dy11**2 - v1*w1*dy11**2 + 2*v2**2*w2*dv2 + 2*v1*v2*w1*dv2 + 2*v1*v2*w2*dv1 + 2*v1**2*w1*dv1 - 4*y21*v1*w1*dy21 + 4*y11*v2*w1*dy21 - 4*y12*v2*w2*dy12 - 4*y11*v1*w2*dy12 + 2*y21*v1*w2*dy11 - 2*y12*v2*w1*dy11 - 2*y11*v2*w2*dy11 - 2*y11*v1*w1*dy11 + 2*v2*w2 + 2*v1*w1

order_D = 3

f11 = -2*y12*v2*w2 - 2*y11*v1*w2
f12 = 2*y12*v2*w1 + 2*y11*v1*w1
f21 = -2*y21*v1*w2 + 2*y11*v2*w2
f22 = 2*y21*v1*w1 - 2*y11*v2*w1
D_abc = -2*a**2*b**2*db*dc**2 - 2*a*c**2*db*dc**2 - 2*a*b**2*db**3 - 2*c**2*db**3 + a*b**3*da*dc**2 + b*c**2*da*dc**2 + 2*a*b**2*da**2*db + 2*c**2*da**2*db - 8*a*c*db*dc - 8*a*b*db**2 + 4*b*c*da*dc + 2*b**2*da*db + 4*a*b*da**2 + 2*b**2*db - 8*a*db - 4*a*b*da + 6*b*da + 2*b
tup4 = (D, f11, f12, f21, f22, D_abc, order_D)

print()
print('We first double-check the claimed properties for each (D, f11, f12, f21, f22, D_abc)\n')
print('---------------------------------------------------------------------------------------------\n')

for tup in [tup1, tup2, tup3, tup4]:
    D, f11, f12, f21, f22, D_abc, order_D = tup
    print('D is GL_2-invariant because its commutators with E11, E12, E21 and E22 all vanish:')
    print()
    print('[D, E11] =', D*E11 - E11*D)
    print('[D, E12] =', D*E12 - E12*D)
    print('[D, E21] =', D*E21 - E21*D)
    print('[D, E22] =', D*E22 - E22*D)
    print()
    print('D_abc is the restriction of D to C[a, b, c] because for each monomial V in C[a, b, c] of degree <= order(D), the difference ρ(D(V)) - D_abc(ρ(V)) is 0:')
    print()
    monomials = [Rabc.one(), a, b, c, a**2, b**2, c**2, a*b, a*c, b*c, a**3, b**3, c**3, a**2*b, a**2*c, a*b**2, b**2*c, a*c**2, b*c**2, a*b*c]
    for V in monomials:
        print(D_abc.diff(V).subs(rho) - D.diff(V.subs(rho)), end = ' ', flush = True)
    print()
    print()
    print('D annihilates Orb(-, (y12 - y21).φ) because of the following vanishing:')
    print()
    result = apply_to_Gaussian(D, (y12 - y21)) + apply_to_Gaussian(E11, f11) + apply_to_Gaussian(E12, f12) + apply_to_Gaussian(E21, f21) + apply_to_Gaussian(E22, f22)
    print('D((y12 - y21).φ) + E11(f11.φ) + E12(f12.φ) + E21(f21.φ) + E22(f22.φ) =', result)
    print('\n---------------------------------------------------------------------------------------------\n')

print('We print the operators D_abc:')
print()
print('(1)', tup1[-2])
print()
print('(2)', tup2[-2])
print()
print('(3)', tup3[-2])
print()
print('(4)', tup4[-2])
print('\n---------------------------------------------------------------------------------------------\n')

############################# §3 Proof of analyticity #################################

print('We are only interested in the principal symbols of these, meaning the top degree terms in da, db, dc. These are')

# It is trivial to do this by hand. We use use the following function only for convenience

def build_monomial(W, exp):
    var = W.gens()
    res = W.one()
    for v, e in zip(var, exp[0] + exp[1]):
        if e > 0:
            res = res * v**e
    return res

def get_princ_symbol(W, D):
    if D == 0:
        return W.zero()

    order = max(sum(dy_degs) for _, dy_degs in D.monomial_coefficients().keys())

    res = W.zero()
    for exp, coeff in D.monomial_coefficients().items():
        if sum(exp[1]) == order:
            res += coeff * build_monomial(W, exp)
    return res

print()
print('σ_1 =', get_princ_symbol(Wabc, tup1[-2]))
print()
print('σ_2 =', get_princ_symbol(Wabc, tup2[-2]))
print()
print('σ_3 =', get_princ_symbol(Wabc, tup3[-2]))
print()
print('σ_4 =', get_princ_symbol(Wabc, tup4[-2]))
print('\n---------------------------------------------------------------------------------------------')

proof = """
We can now prove that Orb(-, (y12 - y21).φ) is analytic on the domain {Δ > 0, a nonzero, c nonzero}. For this we view σ_1, ..., σ_4 as polynomials in the six variables a, b, c, da, db, dc. We need to check that for all a, b, c of the domain, every real solution da, db, dc of

σ_1(a, b, c, da, db, dc) = 0
σ_2(a, b, c, da, db, dc) = 0
σ_3(a, b, c, da, db, dc) = 0
σ_4(a, b, c, da, db, dc) = 0

is either the trivial solution da = db = dc = 0, or satisfies da*db*dc nonzero.

Proof. Assume that σ_1 = ... = σ_4 = 0 and dc = 0. Then σ_2 = 0 implies that da = 0 because a is nonzero. Substituting da = dc = 0 in σ_4 = 0 gives -2*Δ db^3 = 0. Since Δ is nonzero, this implies db = 0 and hence that (da, db, dc) is the trivial solution.

Assume that σ_1 = ... = σ_4 = 0 and that dc is nonzero. First assume that b = 0. Substituting b = 0 in σ_1 = 0 gives 2*c*db*dc = 0. Since c is nonzero, this implies db = 0. Substituting db = 0 in σ_3 = 0 gives 2*a*c^2*dc^3 = 0, which implies dc = 0 in contradiction to our assumptions.

Finally, assume that σ_1 = ... = σ_4 = 0 and that both dc and b are nonzero. If da or db were 0, then σ_1 = 0 or σ_2 = 0 would imply that dc = 0, in contradiction to assumptions.

In summary, we have shown that every nontrivial solution satisfies da*db*dc nonzero. Q.E.D.
"""

#print(proof)

print()
print()

R = PolynomialRing(QQ, names = ('a', 'b', 'c', 'A', 'aA', 'B', 'bB', 'C', 'δ', 'Δ', 'ε', 'μ'))
a, b, c, A, aA, B, bB, C, δ, Δ, ε, μ = R.gens()

linrels = dict()
linrels[bB] = (-c + ε*δ)*C
linrels[aA] = QQ((1,2))*(-c + μ*δ)*C

σ_3 = 2*a*c**2*C**3 + 6*a*b*c*B*C**2 + 4*a*b**2*B**2*C - 2*c**2*B**2*C - 2*b*c*B**3
bbσ_3 = 2*a*b**2*c**2*C**3 + 6*a*b**2*c*bB*C**2 + 4*a*b**2*bB**2*C - 2*c**2*bB**2*C - 2*c*bB**3
bbσ_3_coeff           = 4*a*b**2*Δ - 2*c*Δ*δ*ε - 2*a*b**2*c*δ*ε + 4*c**2*Δ - 2*c**3*δ*ε
                       #4*a*b**2*Δ + 4*c**2*Δ - 2*c*Δ*δ*ε - 2*a*b**2*c*δ*ε - 2*c**3*δ*ε
bbσ_3_coff_simplified = 4*Δ*δ*(δ - c*ε)

print(b**2*σ_3 - bbσ_3.subs({bB:b*B}))
print(bbσ_3.subs(linrels) - C**3*bbσ_3_coeff.subs({Δ:δ**2}))

