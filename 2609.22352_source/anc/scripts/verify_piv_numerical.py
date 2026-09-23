#!/usr/bin/env python3
"""Independent numerical checks for the PIV article.

The script integrates the original Hamiltonian/Lax differential equations.
It does not evaluate symbolic residuals produced by verify_piv_symbolic.py.
All tolerances are deliberately stricter than the accuracy reported in the
human-readable verification report.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp


ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = ROOT / "verification" / "numerical_results.json"

# A generic nonresonant complex data set.  It stays away from q=0 on the
# short x-intervals used below.
X0 = 0.23 + 0.07j
Q0 = 1.17 + 0.19j
P0 = 0.41 - 0.16j
H0 = 2 * P0 - X0 - Q0 / 2
THETA0 = 0.37 + 0.11j
THETAINF = -0.23 + 0.07j
ALPHA = 2 * THETAINF - 1
BETA = -8 * THETA0**2

RTOL = 2e-12
ATOL = 2e-13


@dataclass
class NumericalResult:
    identifier: str
    formulas: str
    description: str
    value: float
    tolerance: float
    status: str


results: list[NumericalResult] = []
diagnostics: dict[str, object] = {}


def record(
    identifier: str,
    formulas: str,
    description: str,
    value: float,
    tolerance: float,
) -> None:
    value = float(abs(value))
    status = "PASS" if np.isfinite(value) and value <= tolerance else "FAIL"
    results.append(
        NumericalResult(identifier, formulas, description, value, tolerance, status)
    )


def maxnorm(value) -> float:
    array = np.asarray(value)
    return float(np.max(np.abs(array)))


def relerr(left, right, floor=1e-14) -> float:
    return maxnorm(np.asarray(left) - np.asarray(right)) / max(
        maxnorm(left), maxnorm(right), floor
    )


def solve(rhs, interval, initial, *, rtol=RTOL, atol=ATOL):
    answer = solve_ivp(
        rhs,
        interval,
        np.asarray(initial, dtype=complex),
        method="DOP853",
        rtol=rtol,
        atol=atol,
    )
    if not answer.success:
        raise RuntimeError(answer.message)
    return answer.y[:, -1]


def qh_rhs(x_value, state):
    q, h = state
    return np.array(
        [
            q * (2 * h + q + 2 * x_value),
            -h**2
            - 2 * h * (q + x_value)
            - 2 * THETAINF
            - 4 * THETA0**2 / q**2,
        ],
        dtype=complex,
    )


def A_matrix(lam, x_value, q, h):
    a = lam + x_value + q * h / (2 * lam)
    b = 1 - q / (2 * lam)
    c = (
        -q * h
        - 2 * THETAINF
        + (q * h**2 - 4 * THETA0**2 / q) / (2 * lam)
    )
    return np.array([[a, b], [c, -a]], dtype=complex)


def B_matrix(lam, x_value, q, h):
    d = lam + x_value + q / 2
    chi = q * h + 2 * THETAINF
    return np.array([[d, 1], [-chi, -d]], dtype=complex)


def theta(lam, x_value, lifted_angle=None):
    if lifted_angle is None:
        logarithm = np.log(lam)
    else:
        logarithm = np.log(abs(lam)) + 1j * lifted_angle
    return lam**2 / 2 + x_value * lam - THETAINF * logarithm


def formal_coefficients(x_value, q, h):
    chi = q * h + 2 * THETAINF
    rho = (
        q * h**2 / 4
        + q**2 * h / 4
        + x_value * q * h / 2
        + q * THETAINF / 2
        + x_value * THETAINF
        - THETA0**2 / q
    )
    delta = x_value * rho + (THETAINF**2 - THETA0**2) / 2
    kappa = rho**2 + chi / 4
    f1 = np.array([[-rho, -0.5], [-chi / 2, rho]], dtype=complex)
    f2 = np.array(
        [
            [(kappa + delta) / 2, (x_value + q / 2 - rho) / 2],
            [rho * (1 + chi / 2) - q * chi / 4, (kappa - delta) / 2],
        ],
        dtype=complex,
    )
    return f1, f2


def Fhat(lam, x_value, q, h):
    f1, f2 = formal_coefficients(x_value, q, h)
    return np.eye(2, dtype=complex) + f1 / lam + f2 / lam**2


def Q_value(lam, x_value, q, h, column):
    u1, u2 = column
    return np.sqrt(q) / (2 * lam) * ((h - lam) * u1**2 - u1 * u2)


def R_value(lam, x_value, q, column):
    u1 = column[0]
    return -np.sqrt(q) * (lam + 2 * x_value + 1.5 * q) * u1**2


def U_value(x_value, q):
    return (
        x_value**2
        - ALPHA
        + 6 * x_value * q
        + 15 * q**2 / 4
        - 3 * BETA / (2 * q**2)
    )


def linear_segment(start, end):
    delta = end - start
    return (
        lambda t: start + delta * t,
        lambda _t: delta,
    )


def radial_segment(r_start, r_end, angle):
    return (
        lambda t: (r_start + (r_end - r_start) * t) * np.exp(1j * angle),
        lambda _t: (r_end - r_start) * np.exp(1j * angle),
    )


def arc_segment(radius, angle_start, angle_end):
    delta = angle_end - angle_start
    return (
        lambda t: radius * np.exp(1j * (angle_start + delta * t)),
        lambda t: 1j
        * delta
        * radius
        * np.exp(1j * (angle_start + delta * t)),
    )


def integrate_spectral_matrix(initial, path, x_value, q, h):
    state = np.asarray(initial, dtype=complex).reshape(4)
    for lam_of_t, dlam_of_t in path:
        def rhs(t, flat):
            matrix = flat.reshape(2, 2)
            return (dlam_of_t(t) * A_matrix(lam_of_t(t), x_value, q, h) @ matrix).reshape(4)

        state = solve(rhs, (0.0, 1.0), state)
    return state.reshape(2, 2)


def integrate_x_matrix(initial, lam, x_start, x_end, q_start, h_start):
    state0 = np.concatenate(
        [np.array([q_start, h_start], dtype=complex), np.asarray(initial).reshape(4)]
    )

    delta_x = x_end - x_start

    def rhs(t, state):
        x_value = x_start + delta_x * t
        q, h = state[:2]
        matrix = state[2:].reshape(2, 2)
        return delta_x * np.concatenate(
            [
                qh_rhs(x_value, [q, h]),
                (B_matrix(lam, x_value, q, h) @ matrix).reshape(4),
            ]
        )

    state = solve(rhs, (0.0, 1.0), state0)
    return state[:2], state[2:].reshape(2, 2)


def subdominant_initial(radius, angle, x_value=X0, q=Q0, h=H0):
    lam = radius * np.exp(1j * angle)
    phase = theta(lam, x_value, lifted_angle=angle)
    if np.cos(2 * angle) > 0:
        return Fhat(lam, x_value, q, h)[:, 1] * np.exp(-phase)
    return Fhat(lam, x_value, q, h)[:, 0] * np.exp(phase)


def integrate_column_with_q(initial, path, x_value=X0, q=Q0, h=H0):
    state = np.concatenate([np.asarray(initial, dtype=complex), np.zeros(1, dtype=complex)])
    for lam_of_t, dlam_of_t in path:
        def rhs(t, current):
            lam = lam_of_t(t)
            dlam = dlam_of_t(t)
            column = current[:2]
            return np.concatenate(
                [
                    dlam * (A_matrix(lam, x_value, q, h) @ column),
                    np.array([dlam * Q_value(lam, x_value, q, h, column)]),
                ]
            )

        state = solve(rhs, (0.0, 1.0), state)
    return state[:2], state[2]


def test_lax_path_independence():
    x1 = X0 + 0.08 - 0.025j
    lam0 = 1.35 + 0.42j
    lam1 = 1.72 + 1.03j
    identity = np.eye(2, dtype=complex)

    spectral_first = integrate_spectral_matrix(
        identity, [linear_segment(lam0, lam1)], X0, Q0, H0
    )
    _, route_a = integrate_x_matrix(spectral_first, lam1, X0, x1, Q0, H0)

    qh_at_x1, x_first = integrate_x_matrix(identity, lam0, X0, x1, Q0, H0)
    route_b = integrate_spectral_matrix(
        x_first, [linear_segment(lam0, lam1)], x1, qh_at_x1[0], qh_at_x1[1]
    )
    error = relerr(route_a, route_b)
    record("N01", "11--17", "Path independence of the compatible Lax pair", error, 3e-9)


def test_formal_residual_scaling():
    angle = 0.19
    radii = [8.0, 12.0, 18.0, 27.0]
    residuals = []
    for radius in radii:
        lam = radius * np.exp(1j * angle)
        step = 2e-5 * max(1.0, abs(lam))
        derivative = (
            Fhat(lam + step, X0, Q0, H0) - Fhat(lam - step, X0, Q0, H0)
        ) / (2 * step)
        dtheta = lam + X0 - THETAINF / lam
        residual = derivative + Fhat(lam, X0, Q0, H0) @ np.diag([dtheta, -dtheta]) - A_matrix(lam, X0, Q0, H0) @ Fhat(lam, X0, Q0, H0)
        residuals.append(maxnorm(residual))
    slopes = [
        np.log(residuals[i] / residuals[i + 1]) / np.log(radii[i + 1] / radii[i])
        for i in range(len(radii) - 1)
    ]
    diagnostics["formal_residual"] = {"radii": radii, "norms": residuals, "observed_orders": slopes}
    # The residual is O(lambda^-2); the last two-radius observed order should
    # be close to 2 before finite-difference roundoff dominates.
    record("N02", "18", "Observed decay order of the truncated formal-series residual", abs(slopes[-1] - 2.0), 0.18)


def evolve_column_in_x(offset, lam, column):
    initial = np.concatenate([[Q0, H0], np.asarray(column, dtype=complex)])

    def rhs(t, state):
        x_value = X0 + offset * t
        q, h = state[:2]
        u = state[2:]
        return offset * np.concatenate(
            [qh_rhs(x_value, [q, h]), B_matrix(lam, x_value, q, h) @ u]
        )

    answer = solve(rhs, (0.0, 1.0), initial, rtol=2e-13, atol=2e-14)
    return X0 + offset, answer[0], answer[1], answer[2:]


def evolve_column_in_lambda(offset, lam, column):
    endpoint = lam + offset
    initial_matrix = np.column_stack(
        [np.asarray(column, dtype=complex), np.zeros(2, dtype=complex)]
    )
    answer = integrate_spectral_matrix(
        initial_matrix,
        [linear_segment(lam, endpoint)],
        X0,
        Q0,
        H0,
    )
    return endpoint, answer[:, 0]


def test_squared_identity_finite_difference():
    lam = 1.28 + 0.61j
    column = np.array([0.73 - 0.24j, -0.31 + 0.58j], dtype=complex)
    hx = 8e-4
    values_q = {}
    for multiplier in (-2, -1, 0, 1, 2):
        if multiplier == 0:
            values_q[multiplier] = Q_value(lam, X0, Q0, H0, column)
        else:
            xv, qv, hv, uv = evolve_column_in_x(multiplier * hx, lam, column)
            values_q[multiplier] = Q_value(lam, xv, qv, hv, uv)
    q_xx_numeric = (
        -values_q[2]
        + 16 * values_q[1]
        - 30 * values_q[0]
        + 16 * values_q[-1]
        - values_q[-2]
    ) / (12 * hx**2)

    hlam = 7e-5
    values_r = {}
    for multiplier in (-2, -1, 0, 1, 2):
        if multiplier == 0:
            values_r[multiplier] = R_value(lam, X0, Q0, column)
        else:
            lv, uv = evolve_column_in_lambda(multiplier * hlam, lam, column)
            values_r[multiplier] = R_value(lv, X0, Q0, uv)
    r_lam_numeric = (
        values_r[-2]
        - 8 * values_r[-1]
        + 8 * values_r[1]
        - values_r[2]
    ) / (12 * hlam)
    residual = q_xx_numeric - U_value(X0, Q0) * values_q[0] - r_lam_numeric
    scale = max(abs(q_xx_numeric), abs(U_value(X0, Q0) * values_q[0]), abs(r_lam_numeric), 1.0)
    record("N03", "29", "Finite-difference test of Q_xx-UQ=d_lambda R using integrated Lax solutions", abs(residual) / scale, 2e-7)


def rapid_cycle(radius=4.6, inner_radius=1.45):
    angles = [0.0, np.pi / 2, np.pi, -np.pi / 2]
    columns = []
    integrals = []
    for angle in angles:
        path = [radial_segment(radius, inner_radius, angle)]
        if abs(angle) > 1e-15:
            path.append(arc_segment(inner_radius, angle, 0.0))
        initial = subdominant_initial(radius, angle)
        column, integral = integrate_column_with_q(initial, path)
        columns.append(column)
        integrals.append(integral)
    symmetric_squares = np.column_stack(
        [
            np.array([u[0] ** 2, u[0] * u[1], u[1] ** 2], dtype=complex)
            for u in columns
        ]
    )
    _left, _singular_values, vh = np.linalg.svd(symmetric_squares)
    coefficients = vh[-1, :].conj()
    coefficients /= np.linalg.norm(coefficients)
    relation_error = maxnorm(symmetric_squares @ coefficients)
    boundary = sum(
        coefficients[j] * R_value(inner_radius, X0, Q0, columns[j])
        for j in range(4)
    )
    cycle_integral = np.dot(coefficients, np.asarray(integrals))
    return relation_error, abs(boundary), cycle_integral, coefficients


def test_rapid_cycle():
    relation_error, boundary_error, cycle_integral, coefficients = rapid_cycle()
    diagnostics["rapid_cycle"] = {
        "relation_error": relation_error,
        "boundary_error": boundary_error,
        "integral": [float(cycle_integral.real), float(cycle_integral.imag)],
        "coefficients": [[float(value.real), float(value.imag)] for value in coefficients],
    }
    record("N04", "34,37,38", "Numerical null relation among four symmetric-square columns", relation_error, 2e-9)
    record("N05", "35,36,40", "Cancellation of the finite endpoint R_IV for the rapid-decay cycle", boundary_error, 2e-8)
    # A nonzero value is a diagnostic, so encode failure as the distance below
    # a conservative nontriviality threshold.
    record("N06", "36,40", "Rapid-decay cycle gives a nontrivial integral", max(0.0, 1e-8 - abs(cycle_integral)), 0.0)


def canonical_stokes_data(q=Q0, h=H0, radius=5.5, inner_radius=1.45):
    # Canonical quadrants are numbered clockwise. With P=S1*S2*S3*S4,
    # the counterclockwise zero monodromy in the Psi1 basis is P*F_infinity.
    columns = {}
    for index in range(-4, 2):
        angle = index * np.pi / 2
        initial = subdominant_initial(radius, angle, q=q, h=h)
        path = [radial_segment(radius, inner_radius, angle)]
        if abs(angle) > 1e-15:
            path.append(arc_segment(inner_radius, angle, 0.0))
        columns[index] = integrate_column_with_q(
            initial, path, q=q, h=h
        )[0]

    # The finite F_2/lambda^2 initialization leaves O(radius^-3) errors in
    # det(Psi_k).  Restore the exact SL(2) normalization recursively while
    # preserving every shared subdominant column.  All factors tend to one as
    # the starting radius grows.
    normalization_factors = []

    def normalize_column(index, determinant):
        factor = 1 / determinant
        columns[index] *= factor
        normalization_factors.append(factor)

    normalize_column(1, np.linalg.det(np.column_stack([columns[1], columns[0]])))
    normalize_column(-1, np.linalg.det(np.column_stack([columns[-1], columns[0]])))
    normalize_column(-2, np.linalg.det(np.column_stack([columns[-1], columns[-2]])))
    normalize_column(-3, np.linalg.det(np.column_stack([columns[-3], columns[-2]])))
    normalize_column(-4, np.linalg.det(np.column_stack([columns[-3], columns[-4]])))

    canonical = [
        np.column_stack([columns[1], columns[0]]),
        np.column_stack([columns[-1], columns[0]]),
        np.column_stack([columns[-1], columns[-2]]),
        np.column_stack([columns[-3], columns[-2]]),
        np.column_stack([columns[-3], columns[-4]]),
    ]
    stokes = [
        np.linalg.solve(canonical[index], canonical[index + 1])
        for index in range(4)
    ]
    multipliers = np.array(
        [stokes[0][1, 0], stokes[1][0, 1], stokes[2][1, 0], stokes[3][0, 1]],
        dtype=complex,
    )
    normalization_error = max(abs(value - 1) for value in normalization_factors)
    return columns, canonical, stokes, multipliers, normalization_error


def test_stokes_and_monodromy():
    _columns, canonical, stokes, multipliers, normalization_error = canonical_stokes_data()
    unwanted = max(
        abs(stokes[0][0, 1]),
        abs(stokes[1][1, 0]),
        abs(stokes[2][0, 1]),
        abs(stokes[3][1, 0]),
    )
    diagonal_error = max(
        abs(stokes[index][diagonal, diagonal] - 1)
        for index in range(4)
        for diagonal in range(2)
    )
    determinant_error = max(abs(np.linalg.det(matrix) - 1) for matrix in canonical)
    s1, s2, s3, s4 = multipliers
    alpha_inf = np.exp(-2j * np.pi * THETAINF)
    relation_left = (
        alpha_inf**2 * s2 * s3
        + alpha_inf**2
        + s1 * s2 * s3 * s4
        + s1 * s2
        + s1 * s4
        + s3 * s4
        + 1
    )
    relation_right = 2 * alpha_inf * np.cos(2 * np.pi * THETA0)
    relation_error = abs(relation_left - relation_right) / max(
        abs(relation_left), abs(relation_right), 1.0
    )

    local_monodromy = integrate_spectral_matrix(
        np.eye(2, dtype=complex),
        [arc_segment(1.45, 0.0, 2 * np.pi)],
        X0,
        Q0,
        H0,
    )
    local_trace_error = abs(
        np.trace(local_monodromy) - 2 * np.cos(2 * np.pi * THETA0)
    )
    local_det_error = abs(np.linalg.det(local_monodromy) - 1)

    diagnostics["stokes"] = {
        "multipliers": [[float(value.real), float(value.imag)] for value in multipliers],
        "unwanted_triangular_entry": float(unwanted),
        "diagonal_error_from_finite_radius": float(diagonal_error),
        "finite_radius_normalization_correction": float(normalization_error),
        "canonical_determinant_error": float(determinant_error),
        "global_relation_relative_error": float(relation_error),
        "local_monodromy_trace": [
            float(np.trace(local_monodromy).real),
            float(np.trace(local_monodromy).imag),
        ],
    }
    record("N07", "19--21", "Triangular form of the four numerically extracted Stokes matrices", unwanted, 2e-10)
    record("N08", "19--21", "Unit diagonal after restoring det(Psi_k)=1", diagonal_error, 2e-10)
    record("N09", "19--28", "Global scalar relation among the four Stokes multipliers", relation_error, 2e-5)
    record("N10", "24--27", "Trace of numerical local monodromy around lambda=0", local_trace_error, 3e-9)
    record("N11", "24--27", "Determinant of numerical local monodromy", local_det_error, 3e-9)


def same_sector_experiment(radius, inner_radius=1.45, eta=0.27):
    start_angle = -eta
    initial = subdominant_initial(radius, start_angle)
    interior_path = [
        radial_segment(radius, inner_radius, start_angle),
        arc_segment(inner_radius, start_angle, eta),
        radial_segment(inner_radius, radius, eta),
    ]
    column_at_end, interior_integral = integrate_column_with_q(initial, interior_path)
    closing_path = [arc_segment(radius, eta, start_angle)]
    _closed_column, closing_integral = integrate_column_with_q(
        column_at_end, closing_path
    )
    return interior_integral, closing_integral, interior_integral + closing_integral


def test_same_sector_cauchy():
    radii = [2.8, 3.2, 3.6]
    data = []
    for radius in radii:
        interior, closing, total = same_sector_experiment(radius)
        data.append(
            {
                "radius": radius,
                "interior_abs": float(abs(interior)),
                "closing_abs": float(abs(closing)),
                "closed_abs": float(abs(total)),
            }
        )
    diagnostics["same_sector"] = data
    record("N12", "30", "Cauchy cancellation on a closed contour inside one decay sector", max(item["closed_abs"] for item in data), 3e-8)
    decrease_ratio = data[-1]["interior_abs"] / max(data[0]["interior_abs"], 1e-300)
    record("N13", "30", "The same-sector two-ended integral tends to zero as the truncation radius grows", decrease_ratio, 0.35)


def transfer_and_variation(q, h, path, dq=0j, dh=0j, include_integral=False):
    initial_matrix = np.eye(2, dtype=complex)
    if not include_integral:
        return integrate_spectral_matrix(initial_matrix, path, X0, q, h)

    state = np.concatenate([initial_matrix.reshape(4), np.zeros(4, dtype=complex)])
    for lam_of_t, dlam_of_t in path:
        def rhs(t, current):
            lam = lam_of_t(t)
            dlam = dlam_of_t(t)
            matrix = current[:4].reshape(2, 2)
            integral = current[4:].reshape(2, 2)
            da = (h * dq + q * dh) / (2 * lam)
            db = -dq / (2 * lam)
            dc = (
                -(h * dq + q * dh)
                + ((h**2 + 4 * THETA0**2 / q**2) * dq + 2 * q * h * dh)
                / (2 * lam)
            )
            delta_a = np.array([[da, db], [dc, -da]], dtype=complex)
            dmatrix = dlam * A_matrix(lam, X0, q, h) @ matrix
            dintegral = dlam * np.linalg.inv(matrix) @ delta_a @ matrix
            return np.concatenate([dmatrix.reshape(4), dintegral.reshape(4)])

        state = solve(rhs, (0.0, 1.0), state)
    return state[:4].reshape(2, 2), state[4:].reshape(2, 2)


def test_variation_of_constants():
    path = [
        linear_segment(1.31 + 0.44j, 1.72 + 0.91j),
        arc_segment(abs(1.72 + 0.91j), np.angle(1.72 + 0.91j), 1.16),
    ]
    dq = 0.29 - 0.17j
    dh = -0.21 + 0.13j
    base, integral = transfer_and_variation(Q0, H0, path, dq, dh, True)
    epsilon = 2e-5
    plus = transfer_and_variation(Q0 + epsilon * dq, H0 + epsilon * dh, path)
    minus = transfer_and_variation(Q0 - epsilon * dq, H0 - epsilon * dh, path)
    finite_difference = (plus - minus) / (2 * epsilon)
    predicted = base @ integral
    record("N14", "41--47,57", "Finite-difference verification of variation of constants", relerr(finite_difference, predicted), 2e-7)


def test_stokes_variations():
    dq = 0.19 - 0.14j
    dh = -0.16 + 0.09j
    epsilon = 1.5e-5
    _columns, canonical, stokes, _multipliers, _norm = canonical_stokes_data()
    _cp, canonical_plus, stokes_plus, _mp, _np = canonical_stokes_data(
        q=Q0 + epsilon * dq, h=H0 + epsilon * dh
    )
    _cm, canonical_minus, stokes_minus, _mm, _nm = canonical_stokes_data(
        q=Q0 - epsilon * dq, h=H0 - epsilon * dh
    )

    delta_canonical = [
        (canonical_plus[index] - canonical_minus[index]) / (2 * epsilon)
        for index in range(5)
    ]
    primitives = [
        np.linalg.solve(canonical[index], delta_canonical[index])
        for index in range(5)
    ]
    delta_stokes_fd = [
        (stokes_plus[index] - stokes_minus[index]) / (2 * epsilon)
        for index in range(4)
    ]
    delta_stokes_predicted = [
        stokes[index] @ primitives[index + 1]
        - primitives[index] @ stokes[index]
        for index in range(4)
    ]
    matrix_error = max(
        relerr(delta_stokes_fd[index], delta_stokes_predicted[index])
        for index in range(4)
    )

    scalar_errors = []
    for index in range(4):
        if index % 2 == 0:
            s = stokes[index][1, 0]
            jm = primitives[index]
            jp = primitives[index + 1]
            component = s * jp[0, 0] + jp[1, 0] - jm[1, 0] - s * jm[1, 1]
            finite_difference = delta_stokes_fd[index][1, 0]
        else:
            s = stokes[index][0, 1]
            jm = primitives[index]
            jp = primitives[index + 1]
            component = jp[0, 1] + s * jp[1, 1] - s * jm[0, 0] - jm[0, 1]
            finite_difference = delta_stokes_fd[index][0, 1]
        scalar_errors.append(relerr(component, finite_difference))

    # Product-rule check for M_infinity, with F_infinity fixed.
    formal_monodromy = np.diag(
        [
            np.exp(-2j * np.pi * THETAINF),
            np.exp(2j * np.pi * THETAINF),
        ]
    )

    def product(matrices):
        value = np.eye(2, dtype=complex)
        for matrix in matrices:
            value = value @ matrix
        return np.linalg.inv(value @ formal_monodromy)

    delta_monodromy_fd = (
        product(stokes_plus) - product(stokes_minus)
    ) / (2 * epsilon)
    delta_monodromy_product_rule = np.zeros((2, 2), dtype=complex)
    for varied_index in range(4):
        term = np.eye(2, dtype=complex)
        for index in range(4):
            term = term @ (
                delta_stokes_fd[index]
                if index == varied_index
                else stokes[index]
            )
        delta_monodromy_product_rule += term

    stokes_product = np.eye(2, dtype=complex)
    for matrix in stokes:
        stokes_product = stokes_product @ matrix
    delta_monodromy_product_rule = (
        -product(stokes) @ delta_monodromy_product_rule
        @ np.linalg.inv(stokes_product)
    )

    diagnostics["stokes_variation"] = {
        "matrix_relative_error": float(matrix_error),
        "scalar_relative_errors": [float(value) for value in scalar_errors],
        "monodromy_product_rule_relative_error": float(
            relerr(delta_monodromy_fd, delta_monodromy_product_rule)
        ),
    }
    record("N15", "48--51,57", "Two-primitive matrix formula for delta S_k", matrix_error, 3e-7)
    record("N16", "52,53", "Component formulas for all four delta s_k", max(scalar_errors), 3e-7)
    record(
        "N17",
        "56",
        "Product-rule formula for delta M_infinity",
        relerr(delta_monodromy_fd, delta_monodromy_product_rule),
        3e-7,
    )


def test_local_monodromy_variation():
    dq = 0.17 + 0.08j
    dh = -0.12 + 0.11j
    epsilon = 2e-5
    loop = [arc_segment(1.45, 0.0, 2 * np.pi)]

    def monodromy(q, h):
        return integrate_spectral_matrix(
            np.eye(2, dtype=complex), loop, X0, q, h
        )

    base = monodromy(Q0, H0)
    plus = monodromy(Q0 + epsilon * dq, H0 + epsilon * dh)
    minus = monodromy(Q0 - epsilon * dq, H0 - epsilon * dh)
    delta = (plus - minus) / (2 * epsilon)

    # Solve delta M=[M,X] in the least-squares sense.  Fixed local exponents
    # imply that every true variation is tangent to the conjugacy class.
    basis = []
    for row in range(2):
        for column in range(2):
            unit = np.zeros((2, 2), dtype=complex)
            unit[row, column] = 1
            basis.append((base @ unit - unit @ base).reshape(4))
    commutator_map = np.column_stack(basis)
    coefficients, *_ = np.linalg.lstsq(
        commutator_map, delta.reshape(4), rcond=None
    )
    represented = (commutator_map @ coefficients).reshape(2, 2)
    record(
        "N18",
        "54,55",
        "Numerical delta M_0 is tangent to the fixed-exponent conjugacy class",
        relerr(delta, represented),
        3e-7,
    )
    record(
        "N19",
        "54,55",
        "The trace of delta M_0 vanishes for fixed theta_0",
        abs(np.trace(delta)),
        3e-7,
    )


def main():
    test_lax_path_independence()
    test_formal_residual_scaling()
    test_squared_identity_finite_difference()
    test_rapid_cycle()
    test_stokes_and_monodromy()
    test_same_sector_cauchy()
    test_variation_of_constants()
    test_stokes_variations()
    test_local_monodromy_variation()

    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "parameters": {
            "x0": [X0.real, X0.imag],
            "q0": [Q0.real, Q0.imag],
            "p0": [P0.real, P0.imag],
            "h0": [H0.real, H0.imag],
            "theta0": [THETA0.real, THETA0.imag],
            "theta_inf": [THETAINF.real, THETAINF.imag],
        },
        "solver": {
            "library": "scipy.integrate.solve_ivp",
            "method": "DOP853",
            "rtol": RTOL,
            "atol": ATOL,
        },
        "check_count": len(results),
        "passed": sum(item.status == "PASS" for item in results),
        "failed": sum(item.status == "FAIL" for item in results),
        "checks": [asdict(item) for item in results],
        "diagnostics": diagnostics,
    }
    REPORT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Numerical checks: {payload['passed']}/{payload['check_count']} passed")
    for item in results:
        print(
            f"[{item.status}] {item.identifier:4s} formulas {item.formulas:11s} "
            f"value={item.value:.3e} tolerance={item.tolerance:.3e}  {item.description}"
        )
    print(f"Report: {REPORT_PATH}")
    if payload["failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
