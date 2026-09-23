#!/usr/bin/env python3
"""Pilot comparison; never writes into the submitted article's verification/."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import sys
from time import perf_counter

import numpy as np
import scipy
from scipy.integrate import quad_vec, solve_ivp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import verify_piv_numerical as core
import verify_piv_two_contours as old

PAIRS = ((0, 1), (1, 2), (2, 3), (0, 3))


def symbolic_derivatives():
    q, h, x, lam = sp.symbols("q h x lam")
    a, b = sp.symbols("a b")
    chi = q*h + 2*b
    rho = q*h*h/4 + q*q*h/4 + x*q*h/2 + q*b/2 + x*b - a*a/q
    delta = x*rho + (b*b-a*a)/2
    kap = rho*rho + chi/4
    f1 = sp.Matrix([[-rho, -sp.Rational(1, 2)], [-chi/2, rho]])
    f2 = sp.Matrix([[(kap+delta)/2, (x+q/2-rho)/2],
                    [rho*(1+chi/2)-q*chi/4, (kap-delta)/2]])
    formal = sp.eye(2) + f1/lam + f2/lam**2
    spectral = sp.Matrix([[lam+x+q*h/(2*lam), 1-q/(2*lam)],
                          [-q*h-2*b+(q*h*h-4*a*a/q)/(2*lam),
                           -lam-x-q*h/(2*lam)]])
    args = (lam, x, q, h, a, b)
    return tuple(sp.lambdify(args, item, "numpy", cse=True) for item in
                 (formal.diff(q), formal.diff(h), spectral.diff(q), spectral.diff(h)))


DERIVATIVES = symbolic_derivatives()


def ivp(rhs, interval, initial, tol, **kwargs):
    result = solve_ivp(rhs, interval, np.asarray(initial, complex),
                       rtol=tol, atol=tol/10, **kwargs)
    if not result.success:
        raise RuntimeError(result.message)
    return result


def background(span, tol=3e-14, q0=core.Q0, h0=core.H0):
    def rhs(t, state):
        q, h, logd = state
        return np.r_[core.qh_rhs(core.X0+t, [q, h]), core.X0+t+q/2]
    initial = [q0, h0, 0j]
    branches = {sign: ivp(rhs, (0, sign*span), initial, tol,
                          method="DOP853", dense_output=True) for sign in (-1, 1)}
    return lambda t: branches[1 if t >= 0 else -1].sol(t)


def products(s):
    return np.array([s[a]*s[b] for a, b in PAIRS])


def spectral_data(x, q, h, radius, tol, sensitivity="ode"):
    """Fresh spectral solves; analytic sensitivities, not finite differences.

    Columns are scaled by their outer exponential during integration.
    Determinant normalizations and their derivatives follow the existing
    sector-sharing convention. These constraints are imposed, not tests.
    """
    columns = {}
    for index in range(-4, 2):
        angle = index*np.pi/2
        lam = radius*np.exp(1j*angle)
        which = 0 if index % 2 else 1
        sign = 1 if which == 0 else -1
        factor = np.exp(sign*core.theta(lam, x, angle))
        args = (lam, x, q, h, core.THETA0, core.THETAINF)
        initial = np.column_stack([core.Fhat(lam, x, q, h)[:, which],
                                   DERIVATIVES[0](*args)[:, which],
                                   DERIVATIVES[1](*args)[:, which]])
        path = [core.radial_segment(radius, 1.45, angle)]
        if index:
            path.append(core.arc_segment(1.45, angle, 0))
        current = initial.ravel()
        for lam_fn, dl_fn in path:
            if sensitivity == "quadrature":
                u0 = current.reshape(2, 3)
                def base_rhs(t, u):
                    return dl_fn(t)*(core.A_matrix(lam_fn(t), x, q, h) @ u)
                base = ivp(base_rhs, (0, 1), u0[:, 0], tol,
                           method="DOP853", dense_output=True)
                # Terminal-normalized adjoint transport avoids inverting a
                # badly conditioned forward fundamental matrix in Duhamel's formula.
                def adjoint_rhs(t, flat):
                    return (-dl_fn(t)*flat.reshape(2, 2)
                            @ core.A_matrix(lam_fn(t), x, q, h)).ravel()
                adjoint = ivp(adjoint_rhs, (1, 0), np.eye(2).ravel(), tol,
                              method="DOP853", dense_output=True)
                def integrand(t):
                    z = lam_fn(t)
                    aa = (z, x, q, h, core.THETA0, core.THETAINF)
                    u = base.sol(t)
                    forcing = np.column_stack([DERIVATIVES[j](*aa) @ u for j in (2, 3)])
                    return dl_fn(t)*(adjoint.sol(t).reshape(2, 2) @ forcing)
                integral, _ = quad_vec(integrand, 0, 1, epsabs=tol, epsrel=tol, limit=300)
                variation = adjoint.sol(0).reshape(2, 2) @ u0[:, 1:] + integral
                current = np.column_stack([base.y[:, -1], variation]).ravel()
                continue
            def rhs(t, state):
                z = lam_fn(t)
                u = state.reshape(2, 3)
                deriv = core.A_matrix(z, x, q, h) @ u
                args = (z, x, q, h, core.THETA0, core.THETAINF)
                deriv[:, 1] += DERIVATIVES[2](*args) @ u[:, 0]
                deriv[:, 2] += DERIVATIVES[3](*args) @ u[:, 0]
                return (dl_fn(t)*deriv).ravel()
            current = ivp(rhs, (0, 1), current, tol, method="DOP853").y[:, -1]
        columns[index] = current.reshape(2, 3)*factor

    def normalize(index, left, right):
        u, v = columns[left], columns[right]
        determinant = np.linalg.det(np.column_stack([u[:, 0], v[:, 0]]))
        dd = np.array([np.linalg.det(np.column_stack([u[:, j], v[:, 0]]))
                       + np.linalg.det(np.column_stack([u[:, 0], v[:, j]]))
                       for j in (1, 2)])
        target = columns[index].copy()
        columns[index][:, 0] = target[:, 0]/determinant
        columns[index][:, 1:] = (target[:, 1:]/determinant
                                - np.outer(target[:, 0], dd)/determinant**2)

    for triple in ((1, 1, 0), (-1, -1, 0), (-2, -1, -2),
                   (-3, -3, -2), (-4, -3, -4)):
        normalize(*triple)
    frames = [np.stack([columns[a], columns[b]], axis=1)
              for a, b in ((1, 0), (-1, 0), (-1, -2), (-3, -2), (-3, -4))]
    s, ds = [], []
    for k in range(4):
        left, right = frames[k], frames[k+1]
        matrix = np.linalg.solve(left[:, :, 0], right[:, :, 0])
        entry = (1, 0) if k % 2 == 0 else (0, 1)
        s.append(matrix[entry])
        ds.append([np.linalg.solve(left[:, :, 0], right[:, :, j]
                                   - left[:, :, j] @ matrix)[entry] for j in (1, 2)])
    s, ds = np.asarray(s), np.asarray(ds)
    jac = np.array([s[a]*ds[b]+s[b]*ds[a] for a, b in PAIRS])
    return s, products(s), jac


def tangent_conversion(x, q, h):
    root = np.sqrt(q)
    qp = core.qh_rhs(x, [q, h])[0]
    return np.array([[root, 0], [-qp/(4*q*root)-root/2, 1/(2*root)]])


def contour_matrix(grid, bg, radius, tol, balanced=False):
    start = perf_counter()
    indices = tuple(range(-1, 5))
    outer = {j: radius*np.exp(.5j*np.pi*j) for j in indices}
    q0, h0 = bg(0)[:2]
    initial_columns = [core.subdominant_initial(radius, .5*np.pi*j,
                                               x_value=core.X0, q=q0, h=h0) for j in indices]
    if balanced:
        # Constant-in-x column rescaling preserves the exact normalized F.
        initial_columns = [u/np.linalg.norm(u) for u in initial_columns]
    initial = np.concatenate(initial_columns)
    def rhs(t, state):
        q, h = bg(t)[:2]
        return np.concatenate([core.B_matrix(outer[j], core.X0+t, q, h)
                               @ state[2*k:2*k+2] for k, j in enumerate(indices)])
    span = max(abs(grid))
    branches = {sign: ivp(rhs, (0, sign*span), initial, tol, method="DOP853",
                          dense_output=True) for sign in (-1, 1)}
    coefficients = {}
    quadrature_errors = []
    def sample(t):
        q, h = bg(t)[:2]
        x = core.X0+t
        state = branches[1 if t >= 0 else -1].sol(t)
        answer = []
        for name, spec in old.CYCLES.items():
            cols, integrals = [], []
            for j in spec["indices"]:
                angle = j*np.pi/2
                paths = [core.radial_segment(radius, 1.45, angle)]
                if angle != spec["vertex_angle"]:
                    paths.append(core.arc_segment(1.45, angle, spec["vertex_angle"]))
                position = indices.index(j)
                column = state[2*position:2*position+2]
                integral = np.zeros(2, complex)
                for lam_fn, dl_fn in paths:
                    def spectral_rhs(v, u):
                        return dl_fn(v)*(core.A_matrix(lam_fn(v), x, q, h) @ u)
                    solution = ivp(spectral_rhs, (0, 1), column, tol,
                                   method="DOP853", dense_output=True)
                    def integrand(v):
                        lam = lam_fn(v)
                        u = solution.sol(v)
                        return dl_fn(v)*np.array([core.Q_value(lam, x, q, h, u),
                                                   old.q_x_value(lam, x, q, h, u)])
                    value, error = quad_vec(integrand, 0, 1, epsabs=tol,
                                            epsrel=tol, limit=300)
                    quadrature_errors.append(float(error))
                    integral += value
                    column = solution.y[:, -1]
                cols.append(column)
                integrals.append(integral)
            if name not in coefficients:
                coefficients[name] = old.null_coefficients(cols)
            answer.append(np.asarray(integrals).T @ coefficients[name])
        return np.column_stack(answer)
    phi0 = sample(0.)
    inverse = np.linalg.inv(phi0)
    result = np.asarray([sample(float(t)) @ inverse for t in grid])
    return result, {"seconds": perf_counter()-start,
                    "radius": radius, "balanced_columns": balanced,
                    "initial_basis_condition": float(np.linalg.cond(phi0)),
                    "max_raw_absolute_quad_error_estimate": max(quadrature_errors)}


def rk_matrix(grid, bg, tol, method):
    start = perf_counter()
    def rhs(t, flat):
        q = bg(t)[0]
        a = np.array([[0, 1], [core.U_value(core.X0+t, q), 0]], complex)
        return (a @ flat.reshape(2, 2)).ravel()
    span = max(abs(grid))
    branches = {sign: ivp(rhs, (0, sign*span), np.eye(2).ravel(), tol,
                          method=method, dense_output=True) for sign in (-1, 1)}
    matrix = np.array([branches[1 if t >= 0 else -1].sol(t).reshape(2, 2)
                       for t in grid])
    return matrix, {"seconds": perf_counter()-start,
                    "nfev": sum(s.nfev for s in branches.values())}


def spectral_profile(grid, bg, radius, tol, sensitivity="ode"):
    start = perf_counter()
    stokes, invariants, jacobians = [], [], []
    for t in grid:
        q, h, logd = bg(t)
        s, m, jac = spectral_data(core.X0+t, q, h, radius, tol, sensitivity)
        weights = np.array([2, -2, 2, -2])
        stokes.append(s*np.exp(weights*logd))
        invariants.append(m)
        jacobians.append(jac @ tangent_conversion(core.X0+t, q, h))
    return np.asarray(stokes), np.asarray(invariants), np.asarray(jacobians), perf_counter()-start


def scaled_max(value, baseline):
    return float(np.max(np.abs(value))/max(np.max(np.abs(baseline)), 1e-30))


def summarize(matrix, reference, jac):
    middle = len(matrix)//2
    variation = jac @ matrix
    return {"solution_error_vs_dop853": scaled_max(matrix-reference, reference),
            "monodromy_variation_drift": scaled_max(variation-variation[middle], variation[middle]),
            "wronskian_drift": float(np.max(np.abs(np.linalg.det(matrix)-1))),
            "variation_error_vs_dop853": scaled_max(jac @ (matrix-reference), jac[middle])}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--span", type=float, default=.24)
    parser.add_argument("--points", type=int, default=33)
    parser.add_argument("--case", choices=("original", "second"), default="original")
    parser.add_argument("--output", type=Path, default=Path(__file__).parent/"results/pilot")
    args = parser.parse_args()
    if args.points < 5 or args.points % 2 != 1 or args.span <= 0:
        parser.error("Use a positive span and an odd point count >= 5")
    args.output.mkdir(parents=True, exist_ok=True)
    protected = [ROOT/"piv2026_manuscript.tex", ROOT/"ms_source.zip",
                 ROOT/"ms_submission.zip", *sorted((ROOT/"verification").glob("*"))]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in protected if p.is_file()}
    grid = np.linspace(-args.span, args.span, args.points)
    start = perf_counter()
    q0, p0 = (core.Q0, core.P0) if args.case == "original" else (.85-.12j, .28+.09j)
    h0 = 2*p0-core.X0-q0/2
    bg = background(args.span, q0=q0, h0=h0)
    background_seconds = perf_counter()-start
    reference, ref_cost = rk_matrix(grid, bg, 3e-14, "DOP853")
    profiles, profile_info, profile_arrays = {}, {}, {}
    for radius, tol, sensitivity in ((4.8, 2e-12, "ode"), (6., 2e-12, "ode"),
                                     (7.2, 2e-12, "ode"), (7.2, 2e-13, "ode"),
                                     (7.2, 2e-13, "quadrature")):
        profile_name = f"R{radius:g}_tol{tol:g}_{sensitivity}"
        print(f"Spectral profile {profile_name}", flush=True)
        stokes, m, jac, seconds = spectral_profile(grid, bg, radius, tol, sensitivity)
        profiles[profile_name] = jac
        profile_arrays[f"stokes_{profile_name}"] = stokes
        profile_arrays[f"invariants_{profile_name}"] = m
        mid = len(grid)//2
        profile_info[profile_name] = {"seconds": seconds,
            "base_invariant_drift": scaled_max(m-m[mid], m[mid]),
            "corrected_stokes_drift": scaled_max(stokes-stokes[mid], stokes[mid]),
            "reference_variation_drift": summarize(reference, reference, jac)["monodromy_variation_drift"]}
        alpha = np.exp(-2j*np.pi*core.THETAINF)
        constraint = (alpha**2*m[:, 1]+alpha**2+m[:, 0]*m[:, 2]+m[:, 0]
                      +m[:, 3]+m[:, 2]+1-2*alpha*np.cos(2*np.pi*core.THETA0))
        gradient = np.column_stack([m[:, 2]+1, np.full(len(grid), alpha**2),
                                    m[:, 0]+1, np.ones(len(grid))])
        profile_info[profile_name]["global_relation_absolute_residual"] = float(np.max(abs(constraint)))
        profile_info[profile_name]["linearized_relation_scaled_residual"] = scaled_max(
            np.einsum("ni,nij->nj", gradient, jac), gradient[:, :, None]*jac)
    jac = profiles[profile_name]
    fd_errors = {}
    q, h = bg(0)[:2]
    _, _, jac_qh = spectral_data(core.X0, q, h, 7.2, 2e-12)
    direction = np.array([.19-.14j, -.16+.09j])
    for eps in (1e-3, 1e-4, 1e-5):
        plus = spectral_data(core.X0, *(np.array([q, h])+eps*direction), 7.2, 2e-12)[1]
        minus = spectral_data(core.X0, *(np.array([q, h])-eps*direction), 7.2, 2e-12)[1]
        fd_errors[str(eps)] = scaled_max((plus-minus)/(2*eps)-jac_qh @ direction,
                                        jac_qh @ direction)
    rows, matrices = [], {"reference": reference}
    configs = [("RK45", t, None) for t in (1e-3, 1e-6, 1e-9, 1e-12)]
    configs += [(method, t, 4.8) for method in ("contour", "balanced_contour")
                for t in (1e-8, 1e-10, 3e-13)]
    configs += [("balanced_contour", 3e-13, r) for r in (4.2, 5.4, 6.)]
    for method, tol, radius in configs:
        label = f"{method}_{tol:g}" + (f"_R{radius:g}" if radius else "")
        print(label, flush=True)
        if "contour" in method:
            matrix, cost = contour_matrix(grid, bg, radius, tol,
                                           balanced=method == "balanced_contour")
        else:
            matrix, cost = rk_matrix(grid, bg, tol, method)
        matrices[label] = matrix
        row = {"label": label, "method": method, "tolerance": tol, **cost,
               **summarize(matrix, reference, jac)}
        row["drift_by_spectral_radius"] = {
            str(r): summarize(matrix, reference, j)["monodromy_variation_drift"]
            for r, j in profiles.items()}
        rows.append(row)
        print(json.dumps(row), flush=True)
    reference_check, _ = rk_matrix(grid, bg, 1e-12, "DOP853")
    dense_background = np.array([bg(t) for t in np.linspace(-args.span, args.span, 1001)])
    if np.min(dense_background[:, 0].real) <= 0:
        raise RuntimeError("Pilot requires the background to remain in Re(q)>0 for the chosen square root")
    report = {"status": "pilot; no certified error bounds or speed claims", "case": args.case,
              "initial_data": {name: [float(complex(z).real), float(complex(z).imag)]
                               for name, z in {"x0": core.X0, "q0": q0, "p0": p0,
                                               "theta0": core.THETA0, "theta_infinity": core.THETAINF}.items()},
              "span": args.span, "points": args.points,
              "invariants": ["s1*s2", "s2*s3", "s3*s4", "s1*s4"],
              "normalization": "F(x0)=I in (y,y_prime); invariants use (q,h) sensitivities",
              "spectral_formal_order": 2, "contour_radius": 4.8,
              "background_seconds": background_seconds, "reference": ref_cost,
              "spectral_profiles": profile_info, "sensitivity_finite_difference_errors": fd_errors,
              "quadrature_vs_variational_ode_jacobian": scaled_max(
                  jac-profiles["R7.2_tol2e-13_ode"], jac),
              "reference_tolerance_check": scaled_max(reference-reference_check, reference),
              "sampled_min_real_q": float(np.min(dense_background[:, 0].real)),
              "sampled_min_abs_q": float(np.min(np.abs(dense_background[:, 0]))),
              "code_hashes": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in (Path(__file__), ROOT/"scripts/verify_piv_numerical.py",
                                        ROOT/"scripts/verify_piv_two_contours.py")},
              "comparisons": rows, "versions": {"numpy": np.__version__, "scipy": scipy.__version__,
                                                    "sympy": sp.__version__},
              "protected_file_hashes": hashes}
    for name, digest in hashes.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    (args.output/"results.json").write_text(json.dumps(report, indent=2)+"\n")
    np.savez(args.output/"arrays.npz", grid=grid, jacobian=jac,
             background=np.asarray([bg(t) for t in grid]),
             **{f"J_{name}": j for name, j in profiles.items()}, **profile_arrays, **matrices)
    with (args.output/"comparison.csv").open("w", newline="") as f:
        fields = ["label", "method", "tolerance", "radius", "seconds", "solution_error_vs_dop853",
                  "monodromy_variation_drift", "wronskian_drift", "variation_error_vs_dop853"]
        writer = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    with (args.output/"monodromy_variations.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["method", "x_offset", "invariant", "initial_direction", "real", "imag"])
        for label, matrix in matrices.items():
            variation = jac @ matrix
            for i, t in enumerate(grid):
                for j, name in enumerate(report["invariants"]):
                    for k in range(2):
                        z = variation[i, j, k]
                        writer.writerow([label, t, name, k, z.real, z.imag])
    print(f"Results: {args.output}", flush=True)


if __name__ == "__main__":
    main()
