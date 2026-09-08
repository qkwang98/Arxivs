#!/usr/bin/env python3
"""Exact-arithmetic checks for the paper on 3 x 2 x 2 tensor invariants.

The script reproduces the finite computations used in the manuscript:

  * the common fan of linearity and the 16-element Hilbert basis;
  * Laurent certificates in the initial and three adjacent charts;
  * weight-semigroup uniqueness and square-free anticanonical decompositions;
  * the folded Donaldson--Thomas mutation calculation;
  * the affine-lattice reduction behind the finite sum;
  * independent comparisons with symmetric-group character calculations.

Only Python's standard library and SymPy are required.  Every calculation is
performed over the integers or rational function fields; no floating-point
comparison is used.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Mapping, MutableMapping, Sequence, Tuple

try:
    import sympy as sp
    from sympy.matrices.normalforms import hermite_normal_form, smith_normal_form
    from sympy.polys.domains import ZZ as SYMPY_ZZ
except ImportError as exc:  # pragma: no cover - exercised only on a missing dependency
    raise SystemExit(
        "SymPy is required. Install it with: python -m pip install 'sympy>=1.12'"
    ) from exc


Vector = Tuple[int, ...]
Cone = Tuple[Vector, Vector, Vector]

SCRIPT_VERSION = "1.2"


# ---------------------------------------------------------------------------
# Shared exact data
# ---------------------------------------------------------------------------

E1: Vector = (1, 0, 0)
E2: Vector = (0, 1, 0)
E3: Vector = (0, 0, 1)


def vadd(a: Sequence[int], b: Sequence[int]) -> Vector:
    return tuple(x + y for x, y in zip(a, b))


def vscale(c: int, a: Sequence[int]) -> Vector:
    return tuple(c * x for x in a)


def dot(a: Sequence[int], b: Sequence[int]) -> int:
    return sum(x * y for x, y in zip(a, b))


def det3(cols: Sequence[Sequence[int]]) -> int:
    a, b, c = cols
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - b[0] * (a[1] * c[2] - a[2] * c[1])
        + c[0] * (a[1] * b[2] - a[2] * b[1])
    )


def canonical_cone(rays: Iterable[Vector]) -> Cone:
    data = tuple(sorted(tuple(r) for r in rays))
    if len(data) != 3 or len(set(data)) != 3:
        raise AssertionError(f"not a simplicial 3-cone: {data}")
    return data  # type: ignore[return-value]


# The fourteen normals defining Xi, grouped as A_4,...,A_7.
A_BOUNDARY: Mapping[int, Tuple[Vector, ...]] = {
    4: (
        (0, 0, 0, 1, 0, 0, 0),
        (1, 0, 0, 1, 0, 0, 0),
        (1, 0, 1, 1, 0, 0, 0),
        (1, 0, 2, 1, 0, 0, 0),
        (1, 1, 2, 1, 0, 0, 0),
    ),
    5: (
        (0, 0, 0, 0, 1, 0, 0),
        (0, 1, 0, 0, 1, 0, 0),
        (1, 1, 0, 0, 1, 0, 0),
    ),
    6: (
        (0, 0, 0, 0, 0, 1, 0),
        (1, 0, 0, 0, 0, 1, 0),
        (1, 0, 1, 0, 0, 1, 0),
    ),
    7: (
        (0, 0, 0, 0, 0, 0, 1),
        (0, 0, 1, 0, 0, 0, 1),
        (0, 1, 1, 0, 0, 0, 1),
    ),
}

# Linear forms whose maxima give the four minimal frozen exponents.
PSI_FORMS: Tuple[Tuple[Vector, ...], ...] = (
    ((0, 0, 0), (-1, 0, 0), (-1, 0, -1), (-1, 0, -2), (-1, -1, -2)),
    ((0, 0, 0), (0, -1, 0), (-1, -1, 0)),
    ((0, 0, 0), (-1, 0, 0), (-1, 0, -1)),
    ((0, 0, 0), (0, 0, -1), (0, -1, -1)),
)

STAR_SUBDIVISIONS: Tuple[Tuple[Vector, Vector], ...] = (
    (vscale(-1, E1), E2),
    (E1, vscale(-1, E3)),
    (E1, vadd(E1, vscale(-1, E3))),
    (vscale(-1, E2), E3),
    (E1, vscale(-1, E2)),
    (vscale(-1, E2), vadd(vscale(-1, E2), E3)),
)

H1: Tuple[Vector, ...] = (
    (1, 0, 0, 0, 0, 0, 0),
    (0, 1, 0, 0, 0, 0, 0),
    (0, 0, 1, 0, 0, 0, 0),
    (2, 0, -1, 0, 0, 0, 1),
)
H0: Tuple[Vector, ...] = (
    (0, 0, 0, 1, 0, 0, 0),
    (0, 0, 0, 0, 1, 0, 0),
    (0, 0, 0, 0, 0, 1, 0),
    (0, 0, 0, 0, 0, 0, 1),
    (-1, 1, 0, 1, 0, 1, 0),
    (0, -1, 1, 0, 1, 0, 0),
    (1, -1, 0, 0, 1, 0, 1),
    (1, 0, -1, 1, 0, 0, 1),
)
HM1: Tuple[Vector, ...] = (
    (-1, 0, 0, 1, 1, 1, 0),
    (0, -1, 0, 1, 1, 0, 1),
    (0, 0, -1, 2, 0, 1, 1),
    (0, -2, 1, 0, 2, 0, 1),
)
HILBERT_BASIS: Tuple[Vector, ...] = H1 + H0 + HM1

# Weights of u_1,...,u_13 in the order
# (lambda_1,lambda_2,lambda_3;mu_1,mu_2;nu_1,nu_2).
GENERATOR_WEIGHTS: Tuple[Vector, ...] = (
    (1, 0, 0, 1, 0, 1, 0),   # u1
    (1, 1, 0, 1, 1, 2, 0),   # u2
    (1, 1, 0, 2, 0, 1, 1),   # u3
    (2, 0, 0, 1, 1, 1, 1),   # u4
    (1, 1, 1, 2, 1, 2, 1),   # u5
    (2, 1, 0, 2, 1, 2, 1),   # u6
    (2, 1, 1, 2, 2, 3, 1),   # u7
    (2, 1, 1, 3, 1, 2, 2),   # u8
    (2, 2, 0, 2, 2, 2, 2),   # u9
    (2, 2, 1, 3, 2, 3, 2),   # u10
    (3, 2, 1, 3, 3, 4, 2),   # u11
    (3, 2, 1, 4, 2, 3, 3),   # u12
    (2, 2, 2, 3, 3, 3, 3),   # u13
)

SEED_ORDER = (1, 5, 7, 2, 3, 4, 13)
SEED_WEIGHT_MATRIX: Tuple[Vector, ...] = tuple(GENERATOR_WEIGHTS[i - 1] for i in SEED_ORDER)

OMEGA_D5: Tuple[Vector, ...] = (
    (0, 0, -1, 1, 0),
    (-1, -1, -1, 1, 0),
    (-1, -1, -2, 1, 1),
    (0, -1, -1, 1, 1),
    (0, -1, -1, 1, -1),
    (0, 0, -2, 0, 0),
    (-2, -2, -2, 0, 0),
)

B_U: Tuple[Vector, ...] = (
    (0, -2, 2, -1, 1, -1, 0),
    (2, 0, -2, 1, -1, 0, 1),
    (-2, 2, 0, 0, 0, 1, -1),
)


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


@dataclass
class Report:
    lines: List[str]

    def add(self, text: str = "") -> None:
        self.lines.append(text)
        print(text)

    def section(self, title: str) -> None:
        if self.lines:
            self.add()
        self.add(f"[{title}]")


# ---------------------------------------------------------------------------
# Fan, Hilbert basis, and D5 lattice checks
# ---------------------------------------------------------------------------


def psi(m: Sequence[int]) -> Vector:
    return tuple(max(dot(form, m) for form in forms) for forms in PSI_FORMS)


def in_xi(g: Sequence[int]) -> bool:
    return all(dot(alpha, g) >= 0 for group in A_BOUNDARY.values() for alpha in group)


def initial_orthant_fan() -> Tuple[Cone, ...]:
    cones: List[Cone] = []
    for signs in itertools.product((-1, 1), repeat=3):
        rays = (
            vscale(signs[0], E1),
            vscale(signs[1], E2),
            vscale(signs[2], E3),
        )
        cones.append(canonical_cone(rays))
    return tuple(sorted(set(cones)))


def star_subdivide(cones: Sequence[Cone], face: Tuple[Vector, Vector]) -> Tuple[Cone, ...]:
    a, b = face
    new_ray = vadd(a, b)
    touched = 0
    result: List[Cone] = []
    for cone in cones:
        cset = set(cone)
        if a in cset and b in cset:
            touched += 1
            third = next(r for r in cone if r not in {a, b})
            result.append(canonical_cone((a, new_ray, third)))
            result.append(canonical_cone((new_ray, b, third)))
        else:
            result.append(cone)
    if touched != 2:
        raise AssertionError(f"face {face} belongs to {touched} maximal cones, expected 2")
    return tuple(sorted(set(result)))


def active_form_on_cone(cone: Cone, forms: Sequence[Vector]) -> Vector:
    maxima = [max(dot(f, r) for f in forms) for r in cone]
    candidates = [f for f in forms if [dot(f, r) for r in cone] == maxima]
    if not candidates:
        raise AssertionError(f"maximum is not linear on cone {cone}; values={maxima}")
    return candidates[0]


def check_fan_hilbert(report: Report, output_dir: Path) -> None:
    report.section("fan and Hilbert basis")
    cones = initial_orthant_fan()
    report.add(f"initial orthant fan: {len(cones)} maximal cones")
    subdivision_log: List[dict] = []
    for step, face in enumerate(STAR_SUBDIVISIONS, start=1):
        before = len(cones)
        cones = star_subdivide(cones, face)
        subdivision_log.append(
            {
                "step": step,
                "face": [list(face[0]), list(face[1])],
                "new_ray": list(vadd(*face)),
                "maximal_cones_before": before,
                "maximal_cones_after": len(cones),
            }
        )
        report.add(
            f"star subdivision {step}: {face[0]}, {face[1]} -> {vadd(*face)}; "
            f"{before} -> {len(cones)} cones"
        )

    assert len(cones) == 20
    determinants = [det3(cone) for cone in cones]
    assert all(abs(d) == 1 for d in determinants)
    report.add("all 20 maximal cones are unimodular")

    active_data: List[dict] = []
    for cone in cones:
        active = [active_form_on_cone(cone, forms) for forms in PSI_FORMS]
        active_data.append(
            {"cone": [list(r) for r in cone], "active_forms": [list(f) for f in active]}
        )
    report.add("the four maximum functions are linear on every maximal cone")

    rays = sorted({r for cone in cones for r in cone})
    assert len(rays) == 12
    lifts = {tuple(r) + psi(r) for r in rays}
    expected_nonvertical = set(H1 + H0[4:] + HM1)
    assert lifts == expected_nonvertical
    assert all(in_xi(g) for g in HILBERT_BASIS)
    assert all(sum(g[:3]) in {-1, 0, 1} for g in HILBERT_BASIS)
    report.add("the 12 primitive fan rays lift to the 12 nonvertical Hilbert generators")
    report.add("adding e4,e5,e6,e7 gives exactly the 16 vectors stated in the paper")

    data = {
        "script_version": SCRIPT_VERSION,
        "subdivisions": subdivision_log,
        "rays": [list(r) for r in rays],
        "maximal_cones": [[list(r) for r in cone] for cone in cones],
        "active_forms": active_data,
        "hilbert_basis": [list(g) for g in HILBERT_BASIS],
    }
    (output_dir / "Kron322_fan_certificate.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def psi_d5(weight: Sequence[int]) -> Vector:
    l1, l2, l3, m1, m2, n1, n2 = weight
    size = l1 + l2 + l3
    assert m1 + m2 == size and n1 + n2 == size
    return (-l3, -l2, -l1, m1 + n1 - size, n1 - m1)


def matmul_int(a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]) -> List[List[int]]:
    bt = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) for col in bt] for row in a]


def check_d5_lattice(report: Report) -> None:
    report.section("D5 weight calculation")
    computed = tuple(psi_d5(w) for w in SEED_WEIGHT_MATRIX)
    assert computed == OMEGA_D5
    assert matmul_int(B_U, OMEGA_D5) == [[0] * 5 for _ in range(3)]

    m_b = sp.Matrix(B_U)
    m_o = sp.Matrix(OMEGA_D5)
    assert m_b.rank() == 2
    assert m_o.rank() == 5
    assert m_b.T.nullspace() == [sp.Matrix([1, 1, 1])]

    # The image is Q(D5): every row has even coordinate sum, while the
    # displayed integral combinations give all five simple roots.  The Smith
    # form independently confirms that the image has index two in Z^5.
    assert all(sum(row) % 2 == 0 for row in OMEGA_D5)
    simple_roots = sp.Matrix(
        [
            [1, -1, 0, 0, 0],
            [0, 1, -1, 0, 0],
            [0, 0, 1, -1, 0],
            [0, 0, 0, 1, -1],
            [0, 0, 0, 1, 1],
        ]
    )
    root_coefficients = sp.Matrix(
        [
            [-1, -1, 0, 1, 1, 0, 0],
            [1, -1, 1, -1, 0, 0, 0],
            [-1, 0, 0, 0, 0, 0, 0],
            [1, 1, -1, 0, 0, 0, 0],
            [1, 1, -1, 1, -1, 0, 0],
        ]
    )
    assert root_coefficients * m_o == simple_roots
    smith = smith_normal_form(m_o.T, domain=SYMPY_ZZ)
    assert [smith[i, i] for i in range(5)] == [1, 1, 1, 1, 2]

    # Solve the integral kernel symbolically.  The free variables v6,v7 occur
    # with integral coefficients, so this is an integral, not merely rational,
    # parametrization.  Hermite normal form compares it with im(B_u^T).
    variables = sp.symbols("v1:8", integer=True)
    solution = next(iter(sp.linsolve((m_o.T, sp.zeros(5, 1)), variables)))
    v6, v7 = variables[5], variables[6]
    expected = (2 * v7, 2 * v6, -2 * v6 - 2 * v7, v6 + v7, -v6 - v7, v6, v7)
    assert solution == expected
    kernel_basis = sp.Matrix.hstack(
        sp.Matrix([2, 0, -2, 1, -1, 0, 1]),
        sp.Matrix([0, 2, -2, 1, -1, 1, 0]),
    )
    assert hermite_normal_form(m_b.T) == hermite_normal_form(kernel_basis)

    report.add("Psi sends the seven triple weights to the displayed D5 weight matrix")
    report.add("the five simple roots lie in the image, whose Smith index in Z^5 is two")
    report.add("B_u Omega_D5 = 0, rank(B_u)=2, rank(Omega_D5)=5")
    report.add("symbolic integer-kernel and Hermite-form checks prove exactness")
    report.add("ker(B_u^T) is generated by (1,1,1), as in the exact sequence")


# ---------------------------------------------------------------------------
# Weight-semigroup checks
# ---------------------------------------------------------------------------


def polynomial_degree(weight: Sequence[int]) -> int:
    return sum(weight[:3])


def vsub(a: Sequence[int], b: Sequence[int]) -> Vector:
    return tuple(x - y for x, y in zip(a, b))


def weight_sum(exponents: Sequence[int]) -> Vector:
    out = [0] * 7
    for exponent, weight in zip(exponents, GENERATOR_WEIGHTS):
        for j, value in enumerate(weight):
            out[j] += exponent * value
    return tuple(out)


def semigroup_solutions(target: Vector) -> List[Vector]:
    target_degree = polynomial_degree(target)
    degrees = [polynomial_degree(w) for w in GENERATOR_WEIGHTS]
    solutions: List[Vector] = []
    current = [0] * len(GENERATOR_WEIGHTS)

    def recurse(index: int, residual: Vector, residual_degree: int) -> None:
        if index == len(GENERATOR_WEIGHTS):
            if all(x == 0 for x in residual):
                solutions.append(tuple(current))
            return
        weight = GENERATOR_WEIGHTS[index]
        degree = degrees[index]
        bounds = [residual[j] // weight[j] for j in range(7) if weight[j] > 0]
        max_exp = min(bounds + [residual_degree // degree])
        for exponent in range(max_exp + 1):
            next_residual = tuple(residual[j] - exponent * weight[j] for j in range(7))
            if min(next_residual) < 0:
                break
            current[index] = exponent
            recurse(index + 1, next_residual, residual_degree - exponent * degree)
        current[index] = 0

    recurse(0, target, target_degree)
    return solutions


def exponent_vector(**kwargs: int) -> Vector:
    out = [0] * 13
    for name, exponent in kwargs.items():
        assert name.startswith("u")
        out[int(name[1:]) - 1] = exponent
    return tuple(out)


def is_dominant_triple(weight: Sequence[int]) -> bool:
    l1, l2, l3, m1, m2, n1, n2 = weight
    return (
        l1 >= l2 >= l3 >= 0
        and m1 >= m2 >= 0
        and n1 >= n2 >= 0
        and l1 + l2 + l3 == m1 + m2 == n1 + n2
    )


def check_weight_semigroup(report: Report, output_dir: Path) -> None:
    report.section("weight semigroup")
    checks: Tuple[Tuple[str, Vector, Vector], ...] = (
        ("(210;21;21)", (2, 1, 0, 2, 1, 2, 1), exponent_vector(u6=1)),
        ("(221;32;32)", (2, 2, 1, 3, 2, 3, 2), exponent_vector(u10=1)),
        ("(321;33;42)", (3, 2, 1, 3, 3, 4, 2), exponent_vector(u11=1)),
        ("(321;42;33)", (3, 2, 1, 4, 2, 3, 3), exponent_vector(u12=1)),
        ("(320;32;32)", (3, 2, 0, 3, 2, 3, 2), exponent_vector(u1=1, u9=1)),
        ("(331;43;43)", (3, 3, 1, 4, 3, 4, 3), exponent_vector(u5=1, u9=1)),
        ("(431;44;53)", (4, 3, 1, 4, 4, 5, 3), exponent_vector(u7=1, u9=1)),
        ("(431;53;44)", (4, 3, 1, 5, 3, 4, 4), exponent_vector(u8=1, u9=1)),
    )
    semigroup_output: List[dict] = []
    for label, target, expected in checks:
        solutions = semigroup_solutions(target)
        assert solutions == [expected]
        semigroup_output.append(
            {"weight": label, "target": list(target), "solution": list(expected)}
        )
        monomial = " ".join(
            f"u{i + 1}^{e}" if e != 1 else f"u{i + 1}"
            for i, e in enumerate(expected)
            if e
        )
        report.add(f"{label}: unique monomial {monomial}")

    anticanonical = (6, 4, 2, 7, 5, 7, 5)
    square_free: List[Tuple[int, ...]] = []
    for mask in range(1 << 13):
        subset = tuple(i + 1 for i in range(13) if mask & (1 << i))
        total = [0] * 7
        for i in subset:
            for j, value in enumerate(GENERATOR_WEIGHTS[i - 1]):
                total[j] += value
        if tuple(total) == anticanonical:
            square_free.append(subset)
    assert set(square_free) == {(11, 12), (7, 8, 9), (2, 3, 4, 13)}
    report.add("the anticanonical weight has exactly the three stated square-free decompositions")

    degree_one = {GENERATOR_WEIGHTS[i] for i in range(13) if polynomial_degree(GENERATOR_WEIGHTS[i]) == 1}
    assert degree_one == {GENERATOR_WEIGHTS[0]}
    degree_two_solutions = []
    for target in {
        weight_sum(exponent_vector(u1=2)),
        GENERATOR_WEIGHTS[1],
        GENERATOR_WEIGHTS[2],
        GENERATOR_WEIGHTS[3],
    }:
        degree_two_solutions.extend(semigroup_solutions(target))
    degree_two_weights = {weight_sum(sol) for sol in degree_two_solutions}
    assert degree_two_weights == {
        weight_sum(exponent_vector(u1=2)),
        GENERATOR_WEIGHTS[1],
        GENERATOR_WEIGHTS[2],
        GENERATOR_WEIGHTS[3],
    }
    report.add("the degree-one and degree-two semigroup assertions used in the UFD proof hold")

    differences = (
        vsub(GENERATOR_WEIGHTS[6], GENERATOR_WEIGHTS[0]),   # u7/u1
        vsub(GENERATOR_WEIGHTS[9], GENERATOR_WEIGHTS[0]),   # u10/u1
        vsub(GENERATOR_WEIGHTS[10], GENERATOR_WEIGHTS[4]),  # u11/u5
        vsub(GENERATOR_WEIGHTS[7], GENERATOR_WEIGHTS[6]),   # u8/u7
    )
    assert all(not is_dominant_triple(w) for w in differences)
    report.add("the four quotient weights in the coprimality argument are nondominant")

    (output_dir / "Kron322_weight_semigroup_certificate.json").write_text(
        json.dumps(
            {
                "script_version": SCRIPT_VERSION,
                "unique_monomials": semigroup_output,
                "square_free_anticanonical_decompositions": [list(x) for x in square_free],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


# ---------------------------------------------------------------------------
# Laurent certificates
# ---------------------------------------------------------------------------


def laurent_system() -> Tuple[Mapping[int, sp.Expr], Mapping[str, object]]:
    u1, u2, u3, u4, u5, u7, u13 = sp.symbols("u1 u2 u3 u4 u5 u7 u13")
    u8 = sp.cancel((u4 * u5**2 + u1**2 * u13) / u7)
    u6 = sp.cancel((u3 * u7 - u2 * u8) / u5)
    u9 = sp.cancel((u6**2 + 4 * u2 * u3 * u4) / u1**2)
    u10 = sp.cancel((u2 * u8 + u3 * u7) / u1)
    u11 = sp.cancel((-2 * u2 * u4 * u5 - u6 * u7) / u1)
    u12 = sp.cancel((2 * u3 * u4 * u5 - u6 * u8) / u1)
    expressions: Dict[int, sp.Expr] = {
        1: u1,
        2: u2,
        3: u3,
        4: u4,
        5: u5,
        6: u6,
        7: u7,
        8: u8,
        9: u9,
        10: u10,
        11: u11,
        12: u12,
        13: u13,
    }
    symbols = {
        "u1": u1,
        "u2": u2,
        "u3": u3,
        "u4": u4,
        "u5": u5,
        "u7": u7,
        "u13": u13,
    }
    return expressions, symbols


def is_monomial_in(expr: sp.Expr, allowed: Sequence[sp.Symbol], all_symbols: Sequence[sp.Symbol]) -> bool:
    expr = sp.expand(expr)
    poly = sp.Poly(expr, *all_symbols, domain=sp.QQ)
    if len(poly.terms()) != 1:
        return False
    exponents, _coefficient = poly.terms()[0]
    allowed_set = set(allowed)
    return all(exponent == 0 or symbol in allowed_set for symbol, exponent in zip(all_symbols, exponents))


def check_laurent(report: Report, output_dir: Path) -> None:
    report.section("Laurent certificates")
    expressions, sym = laurent_system()
    u1 = sym["u1"]
    u2 = sym["u2"]
    u3 = sym["u3"]
    u4 = sym["u4"]
    u5 = sym["u5"]
    u7 = sym["u7"]
    u13 = sym["u13"]
    u6, u8, u9, u10, u11, u12 = (expressions[i] for i in (6, 8, 9, 10, 11, 12))

    relations = (
        u3 * u7 - u2 * u8 - u5 * u6,
        u1**2 * u9 - u6**2 - 4 * u2 * u3 * u4,
        u1 * u10 - 2 * u2 * u8 - u5 * u6,
        u1 * u11 + 2 * u2 * u4 * u5 + u6 * u7,
        u1 * u12 - 2 * u3 * u4 * u5 + u6 * u8,
        u1**2 * u13 - u7 * u8 + u4 * u5**2,
    )
    assert all(sp.cancel(relation) == 0 for relation in relations)
    report.add("the six basic relations vanish identically in the initial Laurent chart")

    p1, p5, p7 = sp.symbols("u1p u5p u7p")
    charts = {
        "initial": ({}, (u1, u5, u7)),
        "mutation_at_u1": ({u1: (u2 * u4 * u5**2 + u3 * u7**2) / p1}, (p1, u5, u7)),
        "mutation_at_u5": ({u5: (u1**2 * u2 * u13 - u3 * u7**2) / p5}, (u1, p5, u7)),
        "mutation_at_u7": ({u7: (u4 * u5**2 + u1**2 * u13) / p7}, (u1, u5, p7)),
    }
    all_symbols = (u1, u2, u3, u4, u5, u7, u13, p1, p5, p7)
    certificate_lines: List[str] = []
    for chart_name, (substitution, invertible) in charts.items():
        certificate_lines.append(f"[{chart_name}]")
        for i in range(1, 14):
            expression = sp.factor(sp.cancel(expressions[i].subs(substitution)))
            numerator, denominator = sp.fraction(expression)
            denominator = sp.factor(denominator)
            if not is_monomial_in(denominator, invertible, all_symbols):
                raise AssertionError(
                    f"u{i} is not Laurent in {chart_name}: denominator={denominator}"
                )
            certificate_lines.append(f"u{i} = {sp.sstr(expression)}")
        certificate_lines.append("")
        report.add(f"all thirteen generators are Laurent in {chart_name}")

    assert sp.cancel((u7 * u10 - u1 * u2 * u13) - (u2 * u4 * u5**2 + u3 * u7**2) / u1) == 0
    assert sp.cancel((u1 * u11 + u2 * u4 * u5) - (u1**2 * u2 * u13 - u3 * u7**2) / u5) == 0
    assert sp.cancel(u8 - (u4 * u5**2 + u1**2 * u13) / u7) == 0
    report.add("the three adjacent variables agree with their invariant expressions")

    assert sp.cancel(u9 - (u6**2 + 4 * u2 * u3 * u4) / u1**2) == 0
    assert sp.cancel(u9 - (u10**2 - 4 * u2 * u3 * u13) / u5**2) == 0
    report.add("both discriminant Laurent certificates hold")

    # Appendix E: exact coefficients for the two further coefficient-fiber models.
    e1_u1p = u10
    e1_u2p = u3 * u4
    e1_u3p = u2 * u4
    e1_u6p = u5
    e1_relations = (
        u1 * e1_u1p - u2 * u8 - u3 * u7,
        u2 * e1_u2p - (u1**2 * u9 - u6**2) / 4,
        u3 * e1_u3p - (u1**2 * u9 - u6**2) / 4,
        u6 * e1_u6p - u3 * u7 + u2 * u8,
    )
    assert all(sp.cancel(relation) == 0 for relation in e1_relations)

    e2_u1p = u5 * u9
    e2_u2p = -2 * u3 * u4 * u5 - u6 * u8
    e2_u3p = 2 * u2 * u4 * u5 - u6 * u7
    e2_u5p = u1 * u9
    e2_u6p = -u10
    e2_relations = (
        u1 * e2_u1p - u2 * u12 + u3 * u11,
        u2 * e2_u2p - u1 * u3 * u11 - u5 * u6**2,
        u3 * e2_u3p - u1 * u2 * u12 + u5 * u6**2,
        u5 * e2_u5p - u2 * u12 + u3 * u11,
        u6 * e2_u6p - u2 * u12 - u3 * u11,
    )
    assert all(sp.cancel(relation) == 0 for relation in e2_relations)
    report.add("the corrected exchange coefficients in both Appendix E models hold identically")

    (output_dir / "Kron322_laurent_certificates.txt").write_text(
        "\n".join(certificate_lines).rstrip() + "\n", encoding="utf-8"
    )


# ---------------------------------------------------------------------------
# Folded DT calculation
# ---------------------------------------------------------------------------


DT_MATRIX: Tuple[Vector, ...] = (
    (0, -1, 1, 0, -1, 1, -1, 1, -1, 0, 0),
    (1, 0, -1, 1, 0, -1, 1, -1, 0, 1, 1),
    (-1, 1, 0, -1, 1, 0, 0, 0, 1, -1, 0),
    (0, -1, 1, 0, -1, 1, -1, 1, -1, 0, 0),
    (1, 0, -1, 1, 0, -1, 1, -1, 0, 1, 1),
    (-1, 1, 0, -1, 1, 0, 0, 0, 1, -1, 0),
)
DT_WORD = tuple(i - 1 for i in (1, 3, 2, 4, 6, 5, 1, 6, 4, 3, 2, 5))
DT_TERMINAL_ORDER = tuple(i - 1 for i in (4, 1, 3, 5, 2, 6))


def mutate_matrix(matrix: Sequence[Sequence[int]], k: int) -> List[List[int]]:
    rows, cols = len(matrix), len(matrix[0])
    result = [[0] * cols for _ in range(rows)]
    for i in range(rows):
        for j in range(cols):
            if i == k or j == k:
                result[i][j] = -matrix[i][j]
            else:
                result[i][j] = (
                    matrix[i][j]
                    + max(matrix[i][k], 0) * max(matrix[k][j], 0)
                    - max(-matrix[i][k], 0) * max(-matrix[k][j], 0)
                )
    return result


def relabel_extended_matrix(matrix: Sequence[Sequence[int]], order: Sequence[int]) -> List[List[int]]:
    result: List[List[int]] = []
    for old_i in order:
        row: List[int] = []
        for new_j in range(len(matrix[0])):
            old_j = order[new_j] if new_j < len(order) else new_j
            row.append(matrix[old_i][old_j])
        result.append(row)
    return result


def monomial(expressions: Sequence[sp.Expr], exponents: Sequence[int]) -> sp.Expr:
    result: sp.Expr = sp.Integer(1)
    for expression, exponent in zip(expressions, exponents):
        if exponent:
            result *= expression**exponent
    return result


def check_dt(report: Report) -> None:
    report.section("folded DT transformation")
    matrix: List[List[int]] = [list(row) for row in DT_MATRIX]
    for k in DT_WORD:
        matrix = mutate_matrix(matrix, k)
    terminal = relabel_extended_matrix(matrix, DT_TERMINAL_ORDER)
    for i in range(6):
        assert terminal[i][:10] == list(DT_MATRIX[i][:10])
        assert terminal[i][10] == -DT_MATRIX[i][10]
    report.add("the twelve mutations return the first ten columns and negate the zeta column")

    u1, u5, u7, u2, u3, u4, u13, zeta = sp.symbols(
        "u1 u5 u7 u2 u3 u4 u13 zeta"
    )
    variables: List[sp.Expr] = [u1, u5, u7, u1, u5, u7, u2, u3, u4, u13, zeta]
    matrix = [list(row) for row in DT_MATRIX]
    for k in DT_WORD:
        row = matrix[k]
        positive = monomial(variables, [max(value, 0) for value in row])
        negative = monomial(variables, [max(-value, 0) for value in row])
        variables[k] = sp.cancel((positive + negative) / variables[k])
        matrix = mutate_matrix(matrix, k)

    terminal_variables = [variables[i] for i in DT_TERMINAL_ORDER] + variables[6:]
    expressions, _sym = laurent_system()
    u9_initial = expressions[9]
    ratios = [
        sp.factor(sp.cancel((terminal_variables[i] / base).subs(zeta, -1)))
        for i, base in enumerate((u1, u5, u7))
    ]
    assert sp.cancel(ratios[0] - u9_initial) == 0
    assert sp.cancel(ratios[1] + u9_initial) == 0
    assert sp.cancel(ratios[2] - u9_initial) == 0
    report.add("before coefficient-torus normalization the folded ratios are (u9,-u9,u9)")

    # The normalization changes the middle sign.  Verify the induced formulas
    # for u8 and u9 from the initial Laurent expressions.
    normalized_substitution = {u1: u9_initial * u1, u5: u9_initial * u5, u7: u9_initial * u7}
    u8_initial = expressions[8]
    u8_image = sp.cancel(u8_initial.subs(normalized_substitution, simultaneous=True))
    u9_image = sp.cancel(u9_initial.subs(normalized_substitution, simultaneous=True))
    assert sp.cancel(u8_image - u9_initial * u8_initial) == 0
    assert sp.cancel(u9_image - 1 / u9_initial) == 0
    report.add("after normalization: u1,u5,u7,u8 are multiplied by u9 and u9 maps to u9^{-1}")


# ---------------------------------------------------------------------------
# Finite-sum derivation and independent character checks
# ---------------------------------------------------------------------------


def partitions(n: int, max_part: int | None = None) -> Iterator[Tuple[int, ...]]:
    if n == 0:
        yield ()
        return
    if max_part is None or max_part > n:
        max_part = n
    for first in range(max_part, 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def z_partition(partition: Sequence[int]) -> int:
    result = 1
    for part, multiplicity in Counter(partition).items():
        result *= part**multiplicity * math.factorial(multiplicity)
    return result


@lru_cache(maxsize=None)
def complete_homogeneous_power_sum(n: int) -> Dict[Tuple[int, ...], Fraction]:
    if n < 0:
        return {}
    if n == 0:
        return {(): Fraction(1)}
    return {partition: Fraction(1, z_partition(partition)) for partition in partitions(n)}


def symmetric_polynomial_multiply(
    left: Mapping[Tuple[int, ...], Fraction],
    right: Mapping[Tuple[int, ...], Fraction],
) -> Dict[Tuple[int, ...], Fraction]:
    output: MutableMapping[Tuple[int, ...], Fraction] = {}
    for p, coefficient_p in left.items():
        for q, coefficient_q in right.items():
            monomial_partition = tuple(sorted(p + q, reverse=True))
            output[monomial_partition] = output.get(monomial_partition, Fraction(0)) + coefficient_p * coefficient_q
    return {partition: coefficient for partition, coefficient in output.items() if coefficient}


def permutation_sign(permutation: Sequence[int]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(len(permutation))
        for j in range(i + 1, len(permutation))
    )
    return -1 if inversions % 2 else 1


@lru_cache(maxsize=None)
def schur_power_sum(partition: Tuple[int, ...]) -> Dict[Tuple[int, ...], Fraction]:
    lam = tuple(part for part in partition if part)
    length = len(lam)
    if length == 0:
        return {(): Fraction(1)}
    output: MutableMapping[Tuple[int, ...], Fraction] = {}
    for permutation in itertools.permutations(range(length)):
        indices = [lam[i] - i + permutation[i] for i in range(length)]
        if any(index < 0 for index in indices):
            continue
        term: Dict[Tuple[int, ...], Fraction] = {(): Fraction(permutation_sign(permutation))}
        for index in indices:
            term = symmetric_polynomial_multiply(term, complete_homogeneous_power_sum(index))
        for monomial_partition, coefficient in term.items():
            output[monomial_partition] = output.get(monomial_partition, Fraction(0)) + coefficient
    return {partition_: coefficient for partition_, coefficient in output.items() if coefficient}


@lru_cache(maxsize=None)
def symmetric_group_character(lam: Tuple[int, ...], cycle_type: Tuple[int, ...]) -> int:
    value = schur_power_sum(lam).get(cycle_type, Fraction(0)) * z_partition(cycle_type)
    if value.denominator != 1:
        raise AssertionError(f"nonintegral character value {value} for {lam}, {cycle_type}")
    return value.numerator


def kronecker_character_formula(lam: Tuple[int, ...], mu: Tuple[int, ...], nu: Tuple[int, ...]) -> int:
    size = sum(lam)
    if sum(mu) != size or sum(nu) != size:
        return 0
    value = Fraction(0)
    for cycle_type in partitions(size):
        value += Fraction(
            symmetric_group_character(lam, cycle_type)
            * symmetric_group_character(mu, cycle_type)
            * symmetric_group_character(nu, cycle_type),
            z_partition(cycle_type),
        )
    if value.denominator != 1:
        raise AssertionError(f"nonintegral Kronecker coefficient {value}")
    return value.numerator


def pad(partition: Sequence[int], length: int) -> Tuple[int, ...]:
    return tuple(partition) + (0,) * (length - len(partition))


def ceil_half(integer: int) -> int:
    return -((-integer) // 2)


def closed_sum_formula(lam: Tuple[int, ...], mu: Tuple[int, ...], nu: Tuple[int, ...]) -> int:
    if sum(lam) != sum(mu) or sum(lam) != sum(nu):
        return 0
    if len(lam) > 4 or len(mu) > 2 or len(nu) > 2:
        return 0

    lambda4 = pad(lam, 4)
    mu2 = pad(mu, 2)
    nu2 = pad(nu, 2)
    rectangle = lambda4[3]
    if mu2[1] < 2 * rectangle or nu2[1] < 2 * rectangle:
        return 0

    lambda3 = (
        lambda4[0] - rectangle,
        lambda4[1] - rectangle,
        lambda4[2] - rectangle,
    )
    mu_reduced = (mu2[0] - 2 * rectangle, mu2[1] - 2 * rectangle)
    nu_reduced = (nu2[0] - 2 * rectangle, nu2[1] - 2 * rectangle)

    A = lambda3[0] + 2 * lambda3[1] - mu_reduced[0] - nu_reduced[0]
    level = max(0, (A + 1) // 2)
    L = (lambda3[0] - 2 * level, lambda3[1] - 2 * level, lambda3[2])
    M = (mu_reduced[0] - 2 * level, mu_reduced[1] - 2 * level)
    N = (nu_reduced[0] - 2 * level, nu_reduced[1] - 2 * level)

    if min(L + M + N) < 0:
        return 0
    if not (L[0] >= L[1] >= L[2] and M[0] >= M[1] and N[0] >= N[1]):
        return 0
    if sum(L) != sum(M) or sum(L) != sum(N):
        return 0

    if M[0] - M[1] > N[0] - N[1]:
        M, N = N, M

    a = L[0] - L[1]
    b = L[1] - L[2]
    c = L[2]
    rho = M[0] - M[1]
    h = M[1] - N[1]
    d = M[0] + N[0] - L[0] - 2 * L[1]

    total = 0
    for x in range(0, min(b, rho) + 1):
        m_x = b - h - 2 * x
        lower = max(0, ceil_half(a - d - x), N[1] - 2 * c - x)
        upper = min(0, m_x) + min(a, (a + h + x) // 2, M[1] - L[1] + x)
        total += max(upper - lower + 1, 0)
    return total


def check_affine_finite_sum_derivation(report: Report) -> None:
    L1, L2, L3, M2, N2, x, y = sp.symbols("L1 L2 L3 M2 N2 x y", integer=True)
    total = L1 + L2 + L3
    M1 = total - M2
    N1 = total - N2
    a = L1 - L2
    b = L2 - L3
    c = L3
    h = M2 - N2
    d = M1 + N1 - L1 - 2 * L2
    delta = sp.Matrix(
        [[
            -a - b + h + 2 * x + 2 * y,
            a - d - 2 * y,
            b - h - 2 * x,
            x - b,
            -x,
            -y,
            x + y + c - N2,
        ]]
    )
    W = sp.Matrix(SEED_WEIGHT_MATRIX)
    target = sp.Matrix([[L1, L2, L3, M1, M2, N1, N2]])
    assert all(sp.simplify(value) == 0 for value in list(-delta * W - target))

    inequalities = [
        sp.expand(sum(alpha[j] * delta[0, j] for j in range(7)))
        for group in A_BOUNDARY.values()
        for alpha in group
    ]
    expected = (
        x - b,
        -L1 - L2 + 2 * L3 + M2 - N2 + 3 * x + 2 * y,
        -L1 + L3 + x + 2 * y,
        -a - h - x + 2 * y,
        -L1 - 2 * L3 + 2 * N2 - x,
        -x,
        -L2 - 2 * L3 + M2 + N2 - x - 2 * y,
        -total + 2 * M2 + x,
        -y,
        -L1 + L3 + h + 2 * x + y,
        -a + y,
        L3 - N2 + x + y,
        L2 - M2 - x + y,
        -2 * L3 + N2 - x - y,
    )
    assert all(sp.simplify(left - right) == 0 for left, right in zip(inequalities, expected))
    report.add("the displayed affine inverse satisfies -delta W = shifted weight identically")
    report.add("substitution into all fourteen cone inequalities gives the stated x- and y-bounds")


def check_finite_sum(report: Report, max_size: int) -> None:
    report.section("finite-sum formula")
    check_affine_finite_sum_derivation(report)
    total_checked = 0
    counts_by_size: List[Tuple[int, int]] = []
    for size in range(max_size + 1):
        first_partitions = [p for p in partitions(size) if len(p) <= 4]
        two_row_partitions = [p for p in partitions(size) if len(p) <= 2]
        checked_this_size = 0
        for lam in first_partitions:
            for mu in two_row_partitions:
                for nu in two_row_partitions:
                    expected = kronecker_character_formula(lam, mu, nu)
                    obtained = closed_sum_formula(lam, mu, nu)
                    if expected != obtained:
                        raise AssertionError(
                            f"finite-sum mismatch at size {size}: {lam}, {mu}, {nu}: "
                            f"character={expected}, sum={obtained}"
                        )
                    checked_this_size += 1
        total_checked += checked_this_size
        counts_by_size.append((size, checked_this_size))
        report.add(f"size {size}: checked {checked_this_size} triples")
    report.add(
        f"independent character comparison passed for {total_checked} triples of size <= {max_size}"
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


TASKS = ("fan", "d5", "weights", "laurent", "dt", "finite-sum")


def parse_tasks(value: str) -> Tuple[str, ...]:
    if value == "all":
        return TASKS
    requested = tuple(item.strip() for item in value.split(",") if item.strip())
    unknown = sorted(set(requested) - set(TASKS))
    if unknown:
        raise argparse.ArgumentTypeError(f"unknown task(s): {', '.join(unknown)}")
    return requested


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tasks",
        default="all",
        type=parse_tasks,
        help="comma-separated subset of fan,d5,weights,laurent,dt,finite-sum; default: all",
    )
    parser.add_argument(
        "--max-size",
        type=int,
        default=12,
        help="largest partition size for the independent character comparison (default: 12)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path.cwd(),
        help="directory for the text/JSON certificates (default: current directory)",
    )
    parser.add_argument("--version", action="version", version=SCRIPT_VERSION)
    args = parser.parse_args(argv)
    tasks: Tuple[str, ...] = args.tasks if isinstance(args.tasks, tuple) else parse_tasks(args.tasks)
    if args.max_size < 0:
        parser.error("--max-size must be nonnegative")
    args.output_dir.mkdir(parents=True, exist_ok=True)

    report = Report([])
    report.add(f"Kron322 reproducibility script {SCRIPT_VERSION}")
    report.add(f"Python {platform.python_version()}")
    report.add(f"SymPy {sp.__version__}")
    report.add(f"tasks: {', '.join(tasks)}")

    if "fan" in tasks:
        check_fan_hilbert(report, args.output_dir)
    if "d5" in tasks:
        check_d5_lattice(report)
    if "weights" in tasks:
        check_weight_semigroup(report, args.output_dir)
    if "laurent" in tasks:
        check_laurent(report, args.output_dir)
    if "dt" in tasks:
        check_dt(report)
    if "finite-sum" in tasks:
        check_finite_sum(report, args.max_size)

    report.add()
    report.add("ALL REQUESTED CHECKS PASSED")
    (args.output_dir / "Kron322_reproducibility_report.txt").write_text(
        "\n".join(report.lines) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
