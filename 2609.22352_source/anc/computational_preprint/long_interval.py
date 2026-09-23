#!/usr/bin/env python3
"""Long horizontal continuation with a continuously lifted square root."""
import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np

import compare_monodromy as c


class LiftedBackground:
    def __init__(self, span, tol=3e-14):
        def rhs(t, state):
            q, h = state[:2]
            x = c.core.X0+t
            return np.r_[c.core.qh_rhs(x, [q, h]), x+q/2, 2*h+q+2*x]
        initial = [c.core.Q0, c.core.H0, 0j, np.log(c.core.Q0)]
        self.branches = {
            sign: c.ivp(rhs, (0, sign*span), initial, tol,
                        method="DOP853", dense_output=True)
            for sign in (-1, 1)}

    def state(self, t):
        return self.branches[1 if t >= 0 else -1].sol(t)

    def __call__(self, t):
        return self.state(t)[:3]

    def sheet(self, t):
        state = self.state(t)
        ratio = np.exp(state[3]/2)/np.sqrt(state[0])
        if abs(abs(ratio)-1) > 1e-6 or abs(ratio.imag) > 1e-6:
            raise RuntimeError("Integrated logarithm is inconsistent with q")
        return 1. if ratio.real > 0 else -1.


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--span", type=float, default=6.)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).parent/"results/long_interval_6")
    args = parser.parse_args()
    if args.span < 1:
        parser.error("Long-interval span must be at least 1")
    args.output.mkdir(parents=True, exist_ok=False)
    protected = [c.ROOT/"piv2026_manuscript.tex", c.ROOT/"ms_source.zip",
                 c.ROOT/"ms_submission.zip", *sorted((c.ROOT/"verification").glob("*"))]
    protected_hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in protected if p.is_file()}
    start = perf_counter()
    bg = LiftedBackground(args.span)
    bg_lo = LiftedBackground(args.span, 1e-12)
    grid = np.unique(np.r_[np.linspace(-args.span, args.span, 25), -.62, -.6, .6, .62])
    middle = len(grid)//2
    assert grid[middle] == 0
    dense = np.linspace(-args.span, args.span, 6001)
    states = np.array([bg.state(t) for t in dense])
    q = states[:, 0]
    sheets = np.array([bg.sheet(t) for t in grid])
    log_error = np.max(abs(np.exp(states[:, 3])/q-1))
    reference, ref_cost = c.rk_matrix(grid, bg, 3e-14, "DOP853")
    ref_lo, _ = c.rk_matrix(grid, bg, 1e-12, "DOP853")
    ref_bg_lo, _ = c.rk_matrix(grid, bg_lo, 3e-14, "DOP853")
    arrays = {"grid": grid, "sheets": sheets, "reference": reference,
              "dense_grid": dense, "background_states": states}
    info = {
        "span": args.span, "length": 2*args.span, "points": len(grid),
        "min_sampled_abs_q": float(min(abs(q))), "max_sampled_abs_q": float(max(abs(q))),
        "sampled_cut_crossings": int(np.sum(abs(np.diff(np.angle(q))) > np.pi)),
        "log_consistency_error": float(log_error),
        "background_q_refinement": c.scaled_max(
            np.array([bg(t)[0]-bg_lo(t)[0] for t in dense]), q),
        "reference_refinement": c.scaled_max(reference-ref_lo, reference),
        "background_refinement_effect": c.scaled_max(reference-ref_bg_lo, reference),
        "reference_wronskian_drift": float(max(abs(np.linalg.det(reference)-1))),
        "max_reference_condition": float(max(np.linalg.cond(reference))),
        "profiles": {}, "methods": {}, "errors": {}, "protected_hashes": protected_hashes}
    methods = {}
    def checkpoint():
        (args.output/"results.json").write_text(json.dumps(info, indent=2)+"\n")
        np.savez_compressed(args.output/"arrays.npz", **arrays)
    print("Background and reference ready", flush=True)
    checkpoint()
    for tol in (1e-6, 1e-9, 1e-12):
        name = f"RK45_{tol}"
        methods[name], cost = c.rk_matrix(grid, bg, tol, "RK45")
        info["methods"][name] = cost
    for radius in (5.4, 6.):
        name = f"contour_R{radius}"
        print(f"Computing {name}", flush=True)
        try:
            principal, cost = c.contour_matrix(grid, bg, radius, 3e-14, balanced=True)
            # Both Q and Q_x are proportional to sqrt(q), so the same sheet
            # factor continues both rows; the initial sheet is +1.
            methods[name] = sheets[:, None, None]*principal
            info["methods"][name] = cost
        except (RuntimeError, np.linalg.LinAlgError, FloatingPointError) as exc:
            info["errors"][name] = str(exc)
        checkpoint()
    for name, matrix in methods.items():
        arrays[name] = matrix
    jac = None
    for radius in (7.2, 9.):
        print(f"Monodromy radius {radius}", flush=True)
        mm, jj = [], []
        for k, t in enumerate(grid):
            if k % 5 == 0:
                print(f"  point {k+1}/{len(grid)}, t={t:g}", flush=True)
            try:
                q_t, h_t, _ = bg(t)
                _, m, j = c.spectral_data(c.core.X0+t, q_t, h_t, radius, 2e-13, "quadrature")
                mm.append(m)
                jj.append(sheets[k]*j @ c.tangent_conversion(c.core.X0+t, q_t, h_t))
            except (RuntimeError, np.linalg.LinAlgError, FloatingPointError) as exc:
                info["errors"][f"monitor_R{radius}_t{t}"] = str(exc)
                mm.append(np.full(4, np.nan, complex))
                jj.append(np.full((4, 2), np.nan, complex))
        m, j = np.asarray(mm), np.asarray(jj)
        arrays[f"invariants_R{radius}"] = m
        arrays[f"jac_R{radius}"] = j
        info["profiles"][str(radius)] = {
            "invariant_drift": c.scaled_max(m-m[middle], m[middle]),
            "reference_variation_drift": c.summarize(reference, reference, j)["monodromy_variation_drift"]}
        jac = j
        checkpoint()
    for name, matrix in methods.items():
        info["methods"][name].update(c.summarize(matrix, reference, jac))
        arrays[f"pointwise_relative_error_{name}"] = (
            np.max(abs(matrix-reference), axis=(1, 2))
            / np.maximum(np.max(abs(reference), axis=(1, 2)), 1e-30))
        info["methods"][name]["max_pointwise_relative_error"] = float(
            max(arrays[f"pointwise_relative_error_{name}"]))
    for p, digest in protected_hashes.items():
        if hashlib.sha256(Path(p).read_bytes()).hexdigest() != digest:
            raise RuntimeError(f"Protected file changed: {p}")
    info["seconds"] = perf_counter()-start
    info["source_hashes"] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in (Path(__file__), Path(c.__file__), Path(c.core.__file__), Path(c.old.__file__))}
    info["numpy"], info["scipy"] = np.__version__, c.scipy.__version__
    checkpoint()
    print(json.dumps({k: v for k, v in info.items() if k not in ("protected_hashes", "source_hashes")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
