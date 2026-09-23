#!/usr/bin/env python3
"""Verify two independent contour solutions of the linearized PIV equation."""

from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad_vec, solve_ivp

import verify_piv_numerical as core


ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = ROOT / "verification"
JSON_PATH = OUT_DIR / "two_contour_results.json"
CSV_PATH = OUT_DIR / "piv_two_contour_solutions.csv"
FIGURE_PATH = OUT_DIR / "piv_two_contour_wronskian.pdf"

RADIUS = 4.8
INNER_RADIUS = 1.45
SPAN = 0.048
POINT_COUNT = 33
BRANCH_INDICES = (-1, 0, 1, 2, 3, 4)
CYCLES = {
    "A": {"indices": (-1, 0, 1, 2), "vertex_angle": 0.0},
    "B": {"indices": (1, 2, 3, 4), "vertex_angle": np.pi},
}


def solve_x_family():
    """Evolve the PIV background and all lifted outer Lax columns in x."""
    outer_lambdas = [
        RADIUS * np.exp(0.5j * np.pi * index) for index in BRANCH_INDICES
    ]
    outer_columns = [
        core.subdominant_initial(RADIUS, 0.5 * np.pi * index)
        for index in BRANCH_INDICES
    ]
    initial = np.concatenate(
        [np.array([core.Q0, core.H0], dtype=complex)] + outer_columns
    )

    def rhs(offset, state):
        x_value = core.X0 + offset
        q, h = state[:2]
        derivative = [core.qh_rhs(x_value, [q, h])]
        for position, lam in enumerate(outer_lambdas):
            column = state[2 + 2 * position : 4 + 2 * position]
            derivative.append(core.B_matrix(lam, x_value, q, h) @ column)
        return np.concatenate(derivative)

    common = dict(
        fun=rhs,
        y0=initial,
        method="DOP853",
        rtol=8e-14,
        atol=8e-15,
        dense_output=True,
    )
    forward = solve_ivp(t_span=(0.0, SPAN), **common)
    backward = solve_ivp(t_span=(0.0, -SPAN), **common)
    if not forward.success or not backward.success:
        raise RuntimeError(forward.message if not forward.success else backward.message)
    return forward, backward


def state_at(offset, forward, backward):
    return (forward if offset >= 0 else backward).sol(offset)


def q_x_value(lam, x_value, q, h, column):
    """Evaluate the total x derivative of Q_IV along the Lax flow."""
    q_prime, h_prime = core.qh_rhs(x_value, [q, h])
    u1, u2 = column
    u1_prime, u2_prime = core.B_matrix(lam, x_value, q, h) @ column
    bracket = (h - lam) * u1**2 - u1 * u2
    bracket_prime = (
        h_prime * u1**2
        + 2 * (h - lam) * u1 * u1_prime
        - u1_prime * u2
        - u1 * u2_prime
    )
    return np.sqrt(q) / (2 * lam) * (
        q_prime * bracket / (2 * q) + bracket_prime
    )


def integrate_leg(initial_column, path, x_value, q, h):
    """Continue one Lax column and integrate Q_IV and its x derivative."""
    column = np.asarray(initial_column, dtype=complex)
    integrals = np.zeros(2, dtype=complex)
    for lam_of_t, dlam_of_t in path:
        def rhs(t, current):
            lam = lam_of_t(t)
            return dlam_of_t(t) * (core.A_matrix(lam, x_value, q, h) @ current)

        solution = solve_ivp(
            rhs,
            (0.0, 1.0),
            column,
            method="DOP853",
            rtol=8e-14,
            atol=8e-15,
            dense_output=True,
        )
        if not solution.success:
            raise RuntimeError(solution.message)

        def integrand(t):
            lam = lam_of_t(t)
            current = solution.sol(t)
            factor = dlam_of_t(t)
            return factor * np.array(
                [
                    core.Q_value(lam, x_value, q, h, current),
                    q_x_value(lam, x_value, q, h, current),
                ],
                dtype=complex,
            )

        contribution, _error = quad_vec(
            integrand, 0.0, 1.0, epsabs=2e-13, epsrel=2e-13, limit=350
        )
        integrals += contribution
        column = solution.y[:, -1]
    return column, integrals


def cycle_paths(indices, vertex_angle):
    paths = {}
    for index in indices:
        angle = 0.5 * np.pi * index
        path = [core.radial_segment(RADIUS, INNER_RADIUS, angle)]
        if abs(angle - vertex_angle) > 1e-15:
            path.append(core.arc_segment(INNER_RADIUS, angle, vertex_angle))
        paths[index] = path
    return paths


def outer_column(state, index):
    position = BRANCH_INDICES.index(index)
    return state[2 + 2 * position : 4 + 2 * position]


def symmetric_square_matrix(columns):
    return np.column_stack(
        [
            np.array([u[0] ** 2, u[0] * u[1], u[1] ** 2], dtype=complex)
            for u in columns
        ]
    )


def null_coefficients(columns):
    square = symmetric_square_matrix(columns)
    _left, _singular_values, vh = np.linalg.svd(square)
    coefficients = vh[-1].conj()
    coefficients /= np.linalg.norm(coefficients)
    pivot = np.argmax(np.abs(coefficients))
    coefficients *= np.exp(-1j * np.angle(coefficients[pivot]))
    return coefficients


def sample_cycle(offset, state, name, paths):
    x_value = core.X0 + offset
    q, h = state[:2]
    indices = CYCLES[name]["indices"]
    columns = []
    integrals = []
    outer_boundary = []
    for index in indices:
        initial = outer_column(state, index)
        column, pair = integrate_leg(initial, paths[index], x_value, q, h)
        columns.append(column)
        integrals.append(pair)
        angle = 0.5 * np.pi * index
        lam = RADIUS * np.exp(1j * angle)
        outer_boundary.append(core.R_value(lam, x_value, q, initial))
    return (
        columns,
        np.asarray(integrals),
        np.asarray(outer_boundary),
    )


def fourth_order_second(values, step):
    return (
        -values[4:]
        + 16 * values[3:-1]
        - 30 * values[2:-2]
        + 16 * values[1:-3]
        - values[:-4]
    ) / (12 * step**2)


def normalized_max(residual, terms):
    denominator = max(np.max(np.abs(term)) for term in terms)
    return float(np.max(np.abs(residual)) / max(denominator, 1e-300))


def complex_pairs(values):
    return [[float(value.real), float(value.imag)] for value in values]


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    forward, backward = solve_x_family()
    paths = {
        name: cycle_paths(data["indices"], data["vertex_angle"])
        for name, data in CYCLES.items()
    }

    base_state = state_at(0.0, forward, backward)
    base_samples = {
        name: sample_cycle(0.0, base_state, name, paths[name])
        for name in CYCLES
    }
    coefficients = {
        name: null_coefficients(base_samples[name][0]) for name in CYCLES
    }

    offsets = np.linspace(-SPAN, SPAN, POINT_COUNT)
    step = float(offsets[1] - offsets[0])
    x_values = []
    q_values = []
    y_values = {name: [] for name in CYCLES}
    y_prime_values = {name: [] for name in CYCLES}
    relation_errors = {name: [] for name in CYCLES}
    endpoint_defects = {name: [] for name in CYCLES}

    for offset in offsets:
        state = state_at(float(offset), forward, backward)
        x_value = core.X0 + offset
        q, h = state[:2]
        x_values.append(x_value)
        q_values.append(q)
        for name in CYCLES:
            columns, integrals, outer_boundary = sample_cycle(
                float(offset), state, name, paths[name]
            )
            coeff = coefficients[name]
            relation_errors[name].append(
                np.max(np.abs(symmetric_square_matrix(columns) @ coeff))
            )
            endpoint_defects[name].append(-np.dot(coeff, outer_boundary))
            y_values[name].append(np.dot(coeff, integrals[:, 0]))
            y_prime_values[name].append(np.dot(coeff, integrals[:, 1]))

    x_values = np.asarray(x_values)
    q_values = np.asarray(q_values)
    for name in CYCLES:
        y_values[name] = np.asarray(y_values[name])
        y_prime_values[name] = np.asarray(y_prime_values[name])
        endpoint_defects[name] = np.asarray(endpoint_defects[name])
        normalization = y_values[name][POINT_COUNT // 2]
        y_values[name] /= normalization
        y_prime_values[name] /= normalization
        endpoint_defects[name] /= normalization

    wronskian = (
        y_values["A"] * y_prime_values["B"]
        - y_prime_values["A"] * y_values["B"]
    )
    center = POINT_COUNT // 2
    wronskian_center = wronskian[center]
    wronskian_relative_drift = float(
        np.max(np.abs(wronskian / wronskian_center - 1.0))
    )
    wronskian_scale = np.max(
        np.abs(y_values["A"] * y_prime_values["B"])
        + np.abs(y_prime_values["A"] * y_values["B"])
    )
    scaled_wronskian = float(abs(wronskian_center) / max(wronskian_scale, 1e-300))

    interior = slice(2, -2)
    potential = np.asarray(
        [core.U_value(x, q) for x, q in zip(x_values[interior], q_values[interior])]
    )
    residuals = {}
    residual_relatives = {}
    for name in CYCLES:
        y_second = fourth_order_second(y_values[name], step)
        residuals[name] = y_second - potential * y_values[name][interior]
        residual_relatives[name] = normalized_max(
            residuals[name], [y_second, potential * y_values[name][interior]]
        )

    relation_relative = {}
    endpoint_relative = {}
    for name in CYCLES:
        base_scale = np.max(np.abs(symmetric_square_matrix(base_samples[name][0])))
        relation_relative[name] = float(
            np.max(relation_errors[name]) / max(base_scale, 1e-300)
        )
        endpoint_relative[name] = normalized_max(
            endpoint_defects[name][interior],
            [potential * y_values[name][interior]],
        )

    checks = [
        {
            "identifier": "T01",
            "description": "Both contour periods satisfy y''-U_IV y=0",
            "value": max(residual_relatives.values()),
            "tolerance": 2e-6,
        },
        {
            "identifier": "T02",
            "description": "Both symmetric-square cycle relations persist in x",
            "value": max(relation_relative.values()),
            "tolerance": 2e-9,
        },
        {
            "identifier": "T03",
            "description": "Both finite-radius endpoint defects are negligible",
            "value": max(endpoint_relative.values()),
            "tolerance": 1e-8,
        },
        {
            "identifier": "T04",
            "description": "The Wronskian is constant on the x grid",
            "value": wronskian_relative_drift,
            "tolerance": 2e-8,
        },
        {
            "identifier": "T05",
            "description": "The scaled Wronskian is separated from zero",
            "value": 1e-3 / max(scaled_wronskian, 1e-300),
            "tolerance": 1.0,
        },
    ]
    for item in checks:
        item["status"] = "PASS" if item["value"] <= item["tolerance"] else "FAIL"

    with CSV_PATH.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            [
                "offset",
                "x_real",
                "x_imag",
                "y_A_real",
                "y_A_imag",
                "y_A_prime_real",
                "y_A_prime_imag",
                "y_B_real",
                "y_B_imag",
                "y_B_prime_real",
                "y_B_prime_imag",
                "wronskian_real",
                "wronskian_imag",
            ]
        )
        for index, offset in enumerate(offsets):
            writer.writerow(
                [
                    offset,
                    x_values[index].real,
                    x_values[index].imag,
                    y_values["A"][index].real,
                    y_values["A"][index].imag,
                    y_prime_values["A"][index].real,
                    y_prime_values["A"][index].imag,
                    y_values["B"][index].real,
                    y_values["B"][index].imag,
                    y_prime_values["B"][index].real,
                    y_prime_values["B"][index].imag,
                    wronskian[index].real,
                    wronskian[index].imag,
                ]
            )

    fig, axes = plt.subplots(2, 2, figsize=(10.0, 6.4), constrained_layout=True)
    for axis, name in zip(axes[0], ("A", "B")):
        axis.plot(offsets, y_values[name].real, color="black", linestyle="-")
        axis.plot(offsets, y_values[name].imag, color="black", linestyle="--")
        axis.set_xlabel(r"$s$, where $x=x_0+s$")
        axis.set_ylabel(rf"$y_{name}(x)$")
        axis.grid(True, color="0.82", linewidth=0.6)
        axis.legend(
            [r"$\operatorname{Re}y$", r"$\operatorname{Im}y$"], frameon=False
        )
    normalized_wronskian = wronskian / wronskian_center
    axes[1, 0].plot(
        offsets, normalized_wronskian.real, color="black", linestyle="-"
    )
    axes[1, 0].plot(
        offsets, normalized_wronskian.imag, color="black", linestyle="--"
    )
    axes[1, 0].set_xlabel(r"$s$, where $x=x_0+s$")
    axes[1, 0].set_ylabel(r"$W(x)/W(x_0)$")
    axes[1, 0].grid(True, color="0.82", linewidth=0.6)
    axes[1, 0].legend(
        [r"$\operatorname{Re}$", r"$\operatorname{Im}$"], frameon=False
    )
    axes[1, 1].semilogy(
        offsets,
        np.maximum(np.abs(normalized_wronskian - 1.0), 1e-18),
        color="black",
    )
    axes[1, 1].set_xlabel(r"$s$, where $x=x_0+s$")
    axes[1, 1].set_ylabel(r"$|W(x)/W(x_0)-1|$")
    axes[1, 1].grid(True, which="both", color="0.82", linewidth=0.6)
    fig.savefig(FIGURE_PATH)
    plt.close(fig)

    payload = {
        "construction": {
            "target_ode_integrated": False,
            "derivatives_from_contour_integrals": True,
            "radius": RADIUS,
            "inner_radius": INNER_RADIUS,
            "point_count": POINT_COUNT,
            "offset_interval": [-SPAN, SPAN],
            "step": step,
            "cycle_A_indices": list(CYCLES["A"]["indices"]),
            "cycle_B_indices": list(CYCLES["B"]["indices"]),
        },
        "coefficients_A": complex_pairs(coefficients["A"]),
        "coefficients_B": complex_pairs(coefficients["B"]),
        "wronskian_at_x0": [
            float(wronskian_center.real),
            float(wronskian_center.imag),
        ],
        "wronskian_absolute_value": float(abs(wronskian_center)),
        "scaled_wronskian": scaled_wronskian,
        "max_relative_wronskian_drift": wronskian_relative_drift,
        "self_adjoint_residuals": residual_relatives,
        "cycle_relation_errors": relation_relative,
        "endpoint_defects": endpoint_relative,
        "checks": checks,
        "passed": sum(item["status"] == "PASS" for item in checks),
        "failed": sum(item["status"] == "FAIL" for item in checks),
        "check_count": len(checks),
    }
    JSON_PATH.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )

    print(f"Two-contour checks: {payload['passed']}/{payload['check_count']} passed")
    for item in checks:
        print(
            f"[{item['status']}] {item['identifier']} value={item['value']:.3e} "
            f"tolerance={item['tolerance']:.3e}  {item['description']}"
        )
    print(
        "W(x0)="
        f"{wronskian_center.real:.12g}{wronskian_center.imag:+.12g}i, "
        f"scaled |W|={scaled_wronskian:.3e}"
    )
    if payload["failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
