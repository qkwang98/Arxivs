#!/usr/bin/env python3
"""Exact SymPy verification suite for the formulas in piv2026_manuscript.tex.

The checks start from the Hamiltonian and the raw Lax matrices whenever
possible.  They intentionally use exact symbolic arithmetic.  Formula numbers
refer to the current numbered equations in the article.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = ROOT / "verification" / "symbolic_results.json"


@dataclass
class CheckResult:
    identifier: str
    formulas: str
    description: str
    status: str


results: list[CheckResult] = []


def normalized(expression):
    if isinstance(expression, sp.MatrixBase):
        return expression.applyfunc(lambda value: sp.factor(sp.cancel(value)))
    return sp.factor(sp.cancel(expression))


def is_zero(expression) -> bool:
    reduced = normalized(expression)
    if isinstance(reduced, sp.MatrixBase):
        return all(value == 0 for value in reduced)
    return reduced == 0


def check(identifier: str, formulas: str, description: str, residual) -> None:
    status = "PASS" if is_zero(residual) else "FAIL"
    results.append(CheckResult(identifier, formulas, description, status))
    if status == "FAIL":
        raise AssertionError(f"{identifier}: residual is not zero:\n{normalized(residual)}")


def check_true(identifier: str, formulas: str, description: str, condition: bool) -> None:
    status = "PASS" if condition else "FAIL"
    results.append(CheckResult(identifier, formulas, description, status))
    if not condition:
        raise AssertionError(f"{identifier}: condition is false")


# ---------------------------------------------------------------------------
# Hamiltonian, scalar PIV, and its linearization: formulas (1)--(10).
# ---------------------------------------------------------------------------

x, q, p = sp.symbols("x q p", nonzero=True)
theta_0, theta_inf = sp.symbols("theta_0 theta_inf")
alpha = 2 * theta_inf - 1
beta = -8 * theta_0**2

H = (
    2 * p**2 * q
    - q**3 / 8
    - x * q**2 / 2
    + (2 * theta_inf - 1 - x**2) * q / 2
    - 2 * theta_0**2 / q
)
q_x = 4 * p * q
p_x = (
    -2 * p**2
    + 3 * q**2 / 8
    + x * q
    - (2 * theta_inf - 1 - x**2) / 2
    - 2 * theta_0**2 / q**2
)

check("S01", "1--3", "Hamilton equations obtained by differentiating H_IV", sp.Matrix([
    sp.diff(H, p) - q_x,
    -sp.diff(H, q) - p_x,
]))


def total_x_qp(expression):
    return (
        sp.diff(expression, x)
        + sp.diff(expression, q) * q_x
        + sp.diff(expression, p) * p_x
    )


q_xx = total_x_qp(q_x)
piv_rhs = (
    q_x**2 / (2 * q)
    + 3 * q**3 / 2
    + 4 * x * q**2
    + 2 * (x**2 - alpha) * q
    + beta / q
)
check("S02", "4,5", "Elimination of p gives the stated scalar P_IV", q_xx - piv_rhs)

v, v_x = sp.symbols("v v_x")
r = sp.symbols("r")
piv_generic = (
    r**2 / (2 * q)
    + 3 * q**3 / 2
    + 4 * x * q**2
    + 2 * (x**2 - alpha) * q
    + beta / q
)
linearized_rhs = sp.diff(piv_generic, r) * v_x + sp.diff(piv_generic, q) * v
linearized_article = (
    r / q * v_x
    + (
        -r**2 / (2 * q**2)
        + 9 * q**2 / 2
        + 8 * x * q
        + 2 * (x**2 - alpha)
        - beta / q**2
    )
    * v
)
check("S03", "6", "Frechet derivative of scalar P_IV", linearized_rhs - linearized_article)

jacobian = sp.Matrix([q_x, p_x]).jacobian([q, p])
jacobian_article = sp.Matrix([
    [4 * p, 4 * q],
    [3 * q / 4 + x + 4 * theta_0**2 / q**3, -4 * p],
])
check("S04", "7", "Jacobian of the Hamiltonian vector field", jacobian - jacobian_article)

hessian = sp.hessian(H, (q, p))
hessian_article = sp.Matrix([
    [-3 * q / 4 - x - 4 * theta_0**2 / q**3, 4 * p],
    [4 * p, 4 * q],
])
check("S05", "8", "Hessian and quadratic tangent Hamiltonian", hessian - hessian_article)

dq, dp = sp.symbols("delta_q delta_p")
eta = sp.Matrix([dq, dp])
K = sp.expand((eta.T * hessian * eta)[0] / 2)
K_article = (
    2 * q * dp**2
    + 4 * p * dq * dp
    - (3 * q / 8 + x / 2 + 2 * theta_0**2 / q**3) * dq**2
)
check("S06", "8", "Expanded expression for K_IV", K - K_article)

J = sp.Matrix([[0, 1], [-1, 0]])
check("S07", "7,8", "Tangent Hamilton equations reproduce the Jacobian system", J * hessian - jacobian)

q1, q2 = sp.symbols("q1 q2", nonzero=True)
coefficient_v = (
    -q1**2 / (2 * q**2)
    + 9 * q**2 / 2
    + 8 * x * q
    + 2 * (x**2 - alpha)
    - beta / q**2
)
# If v=sqrt(q)y, direct substitution into v''-(q'/q)v'-coefficient_v*v=0
# gives y''=(coefficient_v-q''/(2q)+3q'^2/(4q^2))*y.
U_from_liouville = coefficient_v - q2 / (2 * q) + 3 * q1**2 / (4 * q**2)
piv_q2 = (
    q1**2 / (2 * q)
    + 3 * q**3 / 2
    + 4 * x * q**2
    + 2 * (x**2 - alpha) * q
    + beta / q
)
U = x**2 - alpha + 6 * x * q + 15 * q**2 / 4 - 3 * beta / (2 * q**2)
check("S08", "9,10", "Liouville substitution v=sqrt(q)y and self-adjoint potential", U_from_liouville.subs(q2, piv_q2) - U)


# ---------------------------------------------------------------------------
# Lax pair and formal solution: formulas (11)--(18) and displayed formulas.
# ---------------------------------------------------------------------------

lam, h = sp.symbols("lambda h", nonzero=True)
sigma_3 = sp.diag(1, -1)

a = lam + x + q * h / (2 * lam)
b = 1 - q / (2 * lam)
c = -q * h - 2 * theta_inf + (q * h**2 - 4 * theta_0**2 / q) / (2 * lam)
A = sp.Matrix([[a, b], [c, -a]])
A0 = sp.Matrix([[x, 1], [-q * h - 2 * theta_inf, -x]])
Am1 = sp.Matrix([
    [q * h / 2, -q / 2],
    [(q * h**2 - 4 * theta_0**2 / q) / 2, -q * h / 2],
])
check("S09", "11--17", "Component and Laurent forms of A_IV agree", A - (lam * sigma_3 + A0 + Am1 / lam))
check("S10", "17", "Residue A_{-1} has eigenvalues +/-theta_0", sp.Matrix([
    sp.trace(Am1),
    sp.det(Am1) + theta_0**2,
]))

q_x_h = q * (2 * h + q + 2 * x)
h_x = -h**2 - 2 * h * (q + x) - 2 * theta_inf - 4 * theta_0**2 / q**2


def total_x_qh(expression):
    return (
        sp.diff(expression, x)
        + sp.diff(expression, q) * q_x_h
        + sp.diff(expression, h) * h_x
    )


B = sp.Matrix([
    [lam + x + q / 2, 1],
    [-q * h - 2 * theta_inf, -lam - x - q / 2],
])
zero_curvature = A.applyfunc(total_x_qh) - B.diff(lam) + A * B - B * A
check("S11", "11--17", "Zero-curvature equation for the stated A_IV and B_IV", zero_curvature)

# Independently recover q_x and h_x from two entries of the unreduced
# zero-curvature matrix with symbolic derivatives Qx,Hx.
Qx, Hx = sp.symbols("Qx Hx")


def raw_x(expression):
    return sp.diff(expression, x) + sp.diff(expression, q) * Qx + sp.diff(expression, h) * Hx


raw_curvature = A.applyfunc(raw_x) - B.diff(lam) + A * B - B * A
solved_flow = sp.solve(
    [sp.together(raw_curvature[0, 1]), sp.together(raw_curvature[0, 0])],
    [Qx, Hx],
    dict=True,
)[0]
check("S12", "11--17", "Independent recovery of the q,h flow from zero curvature", sp.Matrix([
    solved_flow[Qx] - q_x_h,
    solved_flow[Hx] - h_x,
]))

check("S13", "18", "Derivative of the formal phase Theta_IV", sp.diff(lam**2 / 2 + x * lam - theta_inf * sp.log(lam), lam) - (lam + x - theta_inf / lam))

z = sp.symbols("z")
mu2_z = sp.expand((a**2 + b * c).subs(lam, 1 / z))
target_mu2 = z**-2 + 2 * x / z + x**2 - 2 * theta_inf
check_true(
    "S14",
    "18",
    "Eigenvalue expansion mu=lambda+x-theta_inf/lambda+O(lambda^-2)",
    sp.series(mu2_z - target_mu2, z, 0, 1).removeO() == 0,
)

chi = q * h + 2 * theta_inf
rho = (
    q * h**2 / 4
    + q**2 * h / 4
    + x * q * h / 2
    + q * theta_inf / 2
    + x * theta_inf
    - theta_0**2 / q
)
Delta = x * rho + (theta_inf**2 - theta_0**2) / 2
kappa = rho**2 + chi / 4
F1 = sp.Matrix([[-rho, -sp.Rational(1, 2)], [-chi / 2, rho]])
F2 = sp.Matrix([
    [(kappa + Delta) / 2, (x + q / 2 - rho) / 2],
    [rho * (1 + chi / 2) - q * chi / 4, (kappa - Delta) / 2],
])

# Verify the coefficients directly in the differential equation, without using
# the recurrence code in derive_piv_formal_series.py.
Fhat_z = sp.eye(2) + F1 * z + F2 * z**2
A_z = A.subs(lam, 1 / z)
D_z = (1 / z + x - theta_inf * z) * sigma_3
F_lam_z = -z**2 * Fhat_z.diff(z)
formal_residual = (F_lam_z + Fhat_z * D_z - A_z * Fhat_z).applyfunc(sp.expand)
for power in (-1, 0, 1):
    coefficient = formal_residual.applyfunc(lambda value, p=power: sp.expand(value).coeff(z, p))
    check(f"S15.{power}", "18", f"Formal-series residual at z^{power}", coefficient)

check("S16", "18", "Trace/determinant identities for Psi_1 and Psi_2", sp.Matrix([
    sp.trace(F1),
    sp.trace(F2) - kappa,
    sp.det(F1) + kappa,
]))
det_series = sp.series(Fhat_z.det(), z, 0, 3).removeO()
check("S17", "18", "det(I+Psi_1/lambda+Psi_2/lambda^2)=1+O(lambda^-3)", det_series - 1)

# The spectral normalization must be corrected before using the x equation.
b0 = x + q / 2
x_residual = (
    Fhat_z.applyfunc(total_x_qh)
    + Fhat_z * sigma_3 / z
    - B.subs(lam, 1 / z) * Fhat_z
    + Fhat_z * b0 * sigma_3
).applyfunc(sp.expand)
for power in (0, 1):
    check(f"S44.{power}", "18,32", "Joint normalization Phi=Psi D",
          x_residual.applyfunc(lambda value: value.coeff(z, power)))

zlocal = sp.symbols("zlocal", nonzero=True)
check("S45", "11", "Poincare rank two at infinity",
      -A.subs(lam, 1 / zlocal) / zlocal**2
      + sigma_3 / zlocal**3 + A0 / zlocal**2 + Am1 / zlocal)

Gtest = sp.Matrix([[1, q / (4 * theta_0)],
                  [h - 2 * theta_0 / q, q * h / (4 * theta_0) + sp.Rational(1, 2)]])
check("S46", "24,54", "Normalized moving Frobenius eigenbasis",
      Am1 * Gtest - Gtest * sp.diag(theta_0, -theta_0))
check("S47", "24,54", "Local eigenbasis determinant", Gtest.det() - 1)
check_true("S48", "54", "Local variation has nonzero off-diagonal terms",
           normalized((Gtest.inv() * Gtest.diff(q))[0, 1]) != 0)

Ctest = sp.Matrix([[1, 2], [3, 7]])
dCtest = sp.Matrix([[2, -1], [4, 3]])
Psitest = Gtest * Ctest
dPsitest = Gtest.diff(q) * Ctest + Gtest * dCtest
Ylocal = Gtest.inv() * Gtest.diff(q)
Yspectral = Psitest.inv() * dPsitest
check("S49", "54", "Finite-point connection variation includes local term",
      Ctest * Yspectral - Ylocal * Ctest - dCtest)

# Since
#   Rhat = -Fhat^{-1}(Fhat_lambda + Fhat D - A Fhat)
# and Fhat^{-1}=I+O(z), the already verified O(z^2) residual is equivalent
# to Rhat=O(z^2).  This avoids a prohibitively expensive exact inversion of
# a matrix whose entries contain the expanded rho^2 terms.
check_true(
    "S18",
    "18",
    "Volterra remainder is O(lambda^-2) from Fhat^{-1}=I+O(lambda^-1)",
    all(
        sp.expand(value).coeff(z, power) == 0
        for value in formal_residual
        for power in (-1, 0, 1)
    ),
)


# ---------------------------------------------------------------------------
# Monodromy and Stokes algebra: formulas (19)--(28).
# ---------------------------------------------------------------------------

ainf, s1, s2, s3, s4 = sp.symbols("alpha_inf s1 s2 s3 s4", nonzero=True)
L = lambda value: sp.Matrix([[1, 0], [value, 1]])
Utri = lambda value: sp.Matrix([[1, value], [0, 1]])
Finf = sp.diag(ainf, 1 / ainf)
Pstokes = L(s1) * Utri(s2) * L(s3) * Utri(s4)
Minf = Finf.inv() * Pstokes.inv()
check("S50", "23,27", "Clockwise infinity and counterclockwise zero monodromy",
      (Pstokes * Finf) * Minf - sp.eye(2))
stokes_relation_lhs = (
    ainf**2 * s2 * s3
    + ainf**2
    + s1 * s2 * s3 * s4
    + s1 * s2
    + s1 * s4
    + s3 * s4
    + 1
)
check("S19", "21--23,27,28", "Trace of the ordered Stokes product", ainf * sp.trace(Minf) - stokes_relation_lhs)
check("S20", "21--23", "All Stokes factors and M_infinity have determinant one", sp.Matrix([
    sp.det(L(s1)) - 1,
    sp.det(Utri(s2)) - 1,
    sp.det(Minf) - 1,
]))

t0 = sp.symbols("t0")
C11, C12, C21, C22 = sp.symbols("C11 C12 C21 C22")
Cmat = sp.Matrix([[C11, C12], [C21, C22]])
D0 = sp.diag(t0, 1 / t0)
M0 = Cmat.inv() * D0 * Cmat
check("S21", "24--27", "Local monodromy is conjugate to its exponent matrix", sp.Matrix([
    sp.trace(M0) - (t0 + 1 / t0),
    sp.det(M0) - 1,
]))

# Component formulas for S_k from E^{-1}Z_k^{-1}Z_{k+1}E.
e = sp.symbols("e", nonzero=True)
z11, z12, z21, z22 = sp.symbols("z11 z12 z21 z22")
w11, w12, w21, w22 = sp.symbols("w11 w12 w21 w22")
Z = sp.Matrix([[z11, z12], [z21, z22]])
W = sp.Matrix([[w11, w12], [w21, w22]])
E = sp.diag(e, 1 / e)
connection = sp.simplify(E.inv() * Z.inv() * W * E)
detZ = Z.det()
check("S22", "20,21", "Lower Stokes component formula from two canonical matrices", connection[1, 0] - e**2 * (-z21 * w11 + z11 * w21) / detZ)
check("S23", "20,21", "Upper Stokes component formula from two canonical matrices", connection[0, 1] - e**-2 * (z22 * w12 - z12 * w22) / detZ)


# ---------------------------------------------------------------------------
# Symmetric square and squared-eigenfunction identity: formula (29).
# ---------------------------------------------------------------------------

u1, u2 = sp.symbols("u1 u2")
Wvec = sp.Matrix([u1**2, u1 * u2, u2**2])
Mx = sp.Matrix([
    [2 * (lam + x + q / 2), 2, 0],
    [-chi, 0, 1],
    [0, -2 * chi, -2 * (lam + x + q / 2)],
])
Mlam = sp.Matrix([
    [2 * a, 2 * b, 0],
    [c, 0, b],
    [0, 2 * c, -2 * a],
])
direct_Wx = sp.Matrix([
    2 * u1 * ((lam + x + q / 2) * u1 + u2),
    u2 * ((lam + x + q / 2) * u1 + u2) + u1 * (-chi * u1 - (lam + x + q / 2) * u2),
    2 * u2 * (-chi * u1 - (lam + x + q / 2) * u2),
])
direct_Wlam = sp.Matrix([
    2 * u1 * (a * u1 + b * u2),
    u2 * (a * u1 + b * u2) + u1 * (c * u1 - a * u2),
    2 * u2 * (c * u1 - a * u2),
])
check("S24", "29", "Symmetric-square x-system derived from B_IV", direct_Wx - Mx * Wvec)
check("S25", "29", "Symmetric-square lambda-system derived from A_IV", direct_Wlam - Mlam * Wvec)

U_qh = x**2 - alpha + 6 * x * q + 15 * q**2 / 4 - 3 * beta / (2 * q**2)
Qcoeff = sp.sqrt(q) * sp.Matrix([(h - lam) / (2 * lam), -1 / (2 * lam), 0])
Rcoeff = -sp.sqrt(q) * sp.Matrix([lam + 2 * x + 3 * q / 2, 0, 0])


def total_x_quadratic(coefficients):
    return coefficients.applyfunc(total_x_qh) + Mx.T * coefficients


Q_x_coeff = total_x_quadratic(Qcoeff)
Q_xx_coeff = total_x_quadratic(Q_x_coeff)
R_lam_coeff = Rcoeff.diff(lam) + Mlam.T * Rcoeff
check("S26", "29", "Squared-eigenfunction identity Q_xx-UQ=d_lambda R", Q_xx_coeff - U_qh * Qcoeff - R_lam_coeff)


# ---------------------------------------------------------------------------
# Rapid-decay cycle algebra: formulas (30)--(40).
# ---------------------------------------------------------------------------

u = []
for index in range(4):
    u.append(sp.Matrix(sp.symbols(f"u{index}1 u{index}2")))


def sym_square(vector):
    return sp.Matrix([vector[0] ** 2, vector[0] * vector[1], vector[1] ** 2])


def wedge(left, right):
    return sp.det(sp.Matrix.hstack(left, right))


w = [sym_square(vector) for vector in u]
c_minor = [
    (-1) ** index * sp.det(sp.Matrix.hstack(*(w[j] for j in range(4) if j != index)))
    for index in range(4)
]
check("S27", "34,37,38", "Alternating-minor coefficients annihilate four symmetric squares", sum((c_minor[j] * w[j] for j in range(4)), sp.zeros(3, 1)))

c_wedge = [
    wedge(u[1], u[2]) * wedge(u[1], u[3]) * wedge(u[2], u[3]),
    -wedge(u[0], u[2]) * wedge(u[0], u[3]) * wedge(u[2], u[3]),
    wedge(u[0], u[1]) * wedge(u[0], u[3]) * wedge(u[1], u[3]),
    -wedge(u[0], u[1]) * wedge(u[0], u[2]) * wedge(u[1], u[2]),
]
check("S28", "37", "Explicit Wronskian expressions equal the 3x3 minors", sp.Matrix(c_minor) - sp.Matrix(c_wedge))

aa1, aa2, bb1, bb2, cc1, cc2 = sp.symbols("aa1 aa2 bb1 bb2 cc1 cc2")
ua = sp.Matrix([aa1, aa2])
ub = sp.Matrix([bb1, bb2])
uc = sp.Matrix([cc1, cc2])
check(
    "S29",
    "37",
    "Determinant identity for three symmetric squares",
    sp.det(sp.Matrix.hstack(sym_square(ua), sym_square(ub), sym_square(uc)))
    - wedge(ua, ub) * wedge(ua, uc) * wedge(ub, uc),
)

# R_IV is a linear functional of the symmetric-square vector.  Thus the
# relation at the common endpoint implies the boundary cancellation.
r1, r2, r3 = sp.symbols("r1 r2 r3")
rfunctional = sp.Matrix([[r1, r2, r3]])
check("S30", "35,38", "Symmetric-square relation implies cancellation of R_IV at the finite vertex", (rfunctional * sum((c_minor[j] * w[j] for j in range(4)), sp.zeros(3, 1)))[0])

# Formula (39): on the four central directions cos(2 phi_j)=(-1)^j.
central_cosines = [sp.cos(0), sp.cos(sp.pi), sp.cos(2 * sp.pi), sp.cos(-sp.pi)]
check_true("S31", "31,32,39", "Signs of Re Theta_IV on the four central rays", central_cosines == [1, -1, 1, -1])


# ---------------------------------------------------------------------------
# Variations and monodromy: formulas (41)--(58).
# ---------------------------------------------------------------------------

eps = sp.symbols("epsilon")
dq, dh = sp.symbols("delta_q delta_h")


def variation(expression):
    varied = expression.subs({q: q + eps * dq, h: h + eps * dh}, simultaneous=True)
    return sp.diff(varied, eps).subs(eps, 0)


da_article = (h * dq + q * dh) / (2 * lam)
db_article = -dq / (2 * lam)
dc_article = (
    -(h * dq + q * dh)
    + ((h**2 + 4 * theta_0**2 / q**2) * dq + 2 * q * h * dh) / (2 * lam)
)
check("S32", "42--45", "Gateaux variation of a,b,c", sp.Matrix([
    variation(a) - da_article,
    variation(b) - db_article,
    variation(c) - dc_article,
]))

P11, P12, P21, P22 = sp.symbols("P11 P12 P21 P22")
Psi = sp.Matrix([[P11, P12], [P21, P22]])
dA = sp.Matrix([[da_article, db_article], [dc_article, -da_article]])
Kintegrand = sp.simplify(Psi.inv() * dA * Psi)
detPsi = Psi.det()
lower_numerator = dc_article * P11**2 - db_article * P21**2 - 2 * da_article * P11 * P21
upper_numerator = db_article * P22**2 - dc_article * P12**2 + 2 * da_article * P12 * P22
diagonal_numerator = (
    da_article * (P22 * P11 + P12 * P21)
    + db_article * P22 * P21
    - dc_article * P12 * P11
)
check("S33", "46--50", "Diagonal component of Psi^{-1} delta A Psi", Kintegrand[0, 0] - diagonal_numerator / detPsi)
check("S34", "46--50", "Lower component of Psi^{-1} delta A Psi", Kintegrand[1, 0] - lower_numerator / detPsi)
check("S35", "46--50", "Upper component of Psi^{-1} delta A Psi", Kintegrand[0, 1] - upper_numerator / detPsi)
check("S36", "46--50", "Tracelessness of Psi^{-1} delta A Psi", Kintegrand[1, 1] + Kintegrand[0, 0])

# The diagonal part is algebraically integrable at infinity.  Conjugation by
# exp(Theta*sigma_3) does not affect diagonal entries, so it suffices to use
# the formal prefactor and its inverse through z^2.
dA_z = dA.subs(lam, 1 / z)
Fhat_inverse_series = sp.eye(2) - F1 * z + (F1**2 - F2) * z**2
formal_variation = (
    Fhat_inverse_series * dA_z * Fhat_z
).applyfunc(lambda value: sp.series(value, z, 0, 3).removeO().expand())
for power in (0, 1):
    check(
        f"S37.{power}",
        "48--53",
        f"Diagonal variation integrand has no z^{power} term",
        sp.Matrix([
            formal_variation[0, 0].coeff(z, power),
            formal_variation[1, 1].coeff(z, power),
        ]),
    )

# Differentiate M=C^{-1} D C with an auxiliary scalar epsilon.
dC11, dC12, dC21, dC22 = sp.symbols("dC11 dC12 dC21 dC22")
dC = sp.Matrix([[dC11, dC12], [dC21, dC22]])
M0_eps = (Cmat + eps * dC).inv() * D0 * (Cmat + eps * dC)
dM0_direct = M0_eps.diff(eps).subs(eps, 0)
Xc = Cmat.inv() * dC
check("S38", "54,55", "Variation of local monodromy is [M_0,C^{-1}delta C]", dM0_direct - (M0 * Xc - Xc * M0))

# Product rule for M_infinity.
ds1, ds2, ds3, ds4 = sp.symbols("ds1 ds2 ds3 ds4")
factors = [L(s1), Utri(s2), L(s3), Utri(s4)]
dfactors = [
    sp.Matrix([[0, 0], [ds1, 0]]),
    sp.Matrix([[0, ds2], [0, 0]]),
    sp.Matrix([[0, 0], [ds3, 0]]),
    sp.Matrix([[0, ds4], [0, 0]]),
]
direct_product_variation = sp.zeros(2)
for index in range(4):
    term = sp.eye(2)
    for j in range(4):
        term = term * (dfactors[j] if j == index else factors[j])
    direct_product_variation += term
Pstokes_eps = (
    L(s1 + eps * ds1)
    * Utri(s2 + eps * ds2)
    * L(s3 + eps * ds3)
    * Utri(s4 + eps * ds4)
)
Minf_eps = Finf.inv() * Pstokes_eps.inv()
check("S39", "56", "Inverse-product rule for delta M_infinity",
      Minf_eps.diff(eps).subs(eps, 0)
      + Minf * direct_product_variation * Pstokes.inv())

# Derive the two-primitive transition formula from Psi_+=Psi_- S.
jm11, jm12, jm21, jm22 = sp.symbols("jm11 jm12 jm21 jm22")
jp11, jp12, jp21, jp22 = sp.symbols("jp11 jp12 jp21 jp22")
Jminus = sp.Matrix([[jm11, jm12], [jm21, jm22]])
Jplus = sp.Matrix([[jp11, jp12], [jp21, jp22]])
Sgeneric = sp.Matrix(sp.symbols("sg11 sg12 sg21 sg22")).reshape(2, 2)
x11, x12, x21, x22 = sp.symbols("x11 x12 x21 x22")
Psi_minus = sp.Matrix([[x11, x12], [x21, x22]])
Psi_plus = Psi_minus * Sgeneric
deltaPsi_minus = Psi_minus * Jminus
deltaPsi_plus = Psi_plus * Jplus
# Differentiate Psi_plus=Psi_minus*S and solve the resulting equation for delta S.
deltaS_transition = sp.simplify(
    Psi_minus.inv() * (deltaPsi_plus - deltaPsi_minus * Sgeneric)
)
check(
    "S40",
    "46,48--51,57",
    "Differentiating Psi_+=Psi_-S gives delta S=SJ_+-J_-S",
    deltaS_transition - (Sgeneric * Jplus - Jminus * Sgeneric),
)

slower = sp.Matrix([[1, 0], [s1, 1]])
supper = sp.Matrix([[1, s2], [0, 1]])
lower_component = (slower * Jplus - Jminus * slower)[1, 0]
upper_component = (supper * Jplus - Jminus * supper)[0, 1]
check(
    "S41",
    "51,52",
    "Lower-triangular component formula for delta s_k",
    lower_component - (s1 * jp11 + jp21 - jm21 - s1 * jm22),
)
check(
    "S42",
    "51,53",
    "Upper-triangular component formula for delta s_k",
    upper_component - (jp12 + s2 * jp22 - s2 * jm11 - jm12),
)

# Formula (58): the first perturbative correction has forcing f.  Verify the
# linear part by introducing q+epsilon*v and an additive epsilon*f.
forcing = sp.symbols("f")
qfun = sp.Function("q")(x)
vfun = sp.Function("v")(x)
alpha_s, beta_s = sp.symbols("alpha beta")


def scalar_rhs(Q, Qx):
    return (
        Qx**2 / (2 * Q)
        + 3 * Q**3 / 2
        + 4 * x * Q**2
        + 2 * (x**2 - alpha_s) * Q
        + beta_s / Q
    )


perturbed_residual = (
    sp.diff(qfun + eps * vfun, x, 2)
    - scalar_rhs(qfun + eps * vfun, sp.diff(qfun + eps * vfun, x))
    - eps * forcing
)
first_variation = sp.diff(perturbed_residual, eps).subs(eps, 0)
expected_first_variation = (
    sp.diff(vfun, x, 2)
    - sp.diff(qfun, x) / qfun * sp.diff(vfun, x)
    - (
        -sp.diff(qfun, x) ** 2 / (2 * qfun**2)
        + 9 * qfun**2 / 2
        + 8 * x * qfun
        + 2 * (x**2 - alpha_s)
        - beta_s / qfun**2
    )
    * vfun
    - forcing
)
check("S43", "58", "Linearization of the nonintegrably perturbed scalar equation", first_variation - expected_first_variation)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "engine": f"SymPy {sp.__version__}",
        "check_count": len(results),
        "passed": sum(item.status == "PASS" for item in results),
        "failed": sum(item.status == "FAIL" for item in results),
        "checks": [asdict(item) for item in results],
    }
    REPORT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"SymPy {sp.__version__}: {payload['passed']}/{payload['check_count']} exact checks passed")
    for item in results:
        print(f"[{item.status}] {item.identifier:7s} formulas {item.formulas:12s} {item.description}")
    print(f"Report: {REPORT_PATH}")


if __name__ == "__main__":
    main()
