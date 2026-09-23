#!/usr/bin/env python3
"""Continuation stress test on the original background; preserve pilot data."""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
import compare_monodromy as c


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--spans", nargs="+", type=float, default=[.4, .5, .55, .6])
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "results/stress_continuation")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    records, arrays = [], {}
    for span in args.spans:
        print(f"Span {span}", flush=True)
        grid = np.linspace(-span, span, 9)
        bg = c.background(span)
        bg_lo = c.background(span, tol=1e-12)
        dense = np.linspace(-span, span, 2001)
        q = np.array([bg(t)[0] for t in dense])
        # The existing kernels use the principal square root: restrict this test
        # to the right half-plane instead of silently changing its branch.
        if np.min(q.real) <= 0:
            raise RuntimeError("Background leaves the verified square-root chart")
        reference, _ = c.rk_matrix(grid, bg, 3e-14, "DOP853")
        ref_lo, _ = c.rk_matrix(grid, bg, 1e-12, "DOP853")
        ref_bg_lo, _ = c.rk_matrix(grid, bg_lo, 3e-14, "DOP853")
        record = {"span": span, "max_abs_q": float(max(abs(q))),
                  "min_real_q_sampled": float(min(q.real)),
                  "max_reference_condition": float(max(np.linalg.cond(reference))),
                  "reference_refinement": c.scaled_max(reference-ref_lo, reference),
                  "background_refinement_effect": c.scaled_max(reference-ref_bg_lo, reference),
                  "profiles": {}, "methods": {}}
        arrays[f"grid_{span}"] = grid
        arrays[f"reference_{span}"] = reference
        jac = None
        for radius in (6., 7.2):
            print(f"  Monodromy R={radius}", flush=True)
            _, m, jj, seconds = c.spectral_profile(grid, bg, radius, 2e-13, "quadrature")
            record["profiles"][str(radius)] = {
                "invariant_drift": c.scaled_max(m-m[4], m[4]),
                "reference_variation_drift": c.summarize(reference, reference, jj)["monodromy_variation_drift"],
                "seconds": seconds}
            arrays[f"jac_{span}_{radius}"] = jj
            arrays[f"invariants_{span}_{radius}"] = m
            jac = jj
        for tol in (1e-6, 1e-9, 1e-12):
            f, cost = c.rk_matrix(grid, bg, tol, "RK45")
            record["methods"][f"RK45_{tol}"] = {**cost, **c.summarize(f, reference, jac)}
            arrays[f"rk_{span}_{tol}"] = f
        for radius in (5.4, 6.):
            print(f"  Contours R={radius}", flush=True)
            f, cost = c.contour_matrix(grid, bg, radius, 3e-13, balanced=True)
            record["methods"][f"contour_{radius}"] = {**cost, **c.summarize(f, reference, jac)}
            arrays[f"contour_{span}_{radius}"] = f
        records.append(record)
        print(json.dumps(record), flush=True)
        payload = {"records": records, "points_per_span": 9,
                   "numpy": np.__version__, "scipy": c.scipy.__version__,
                   "source_hashes": {str(p.name): hashlib.sha256(p.read_bytes()).hexdigest()
                                     for p in (Path(__file__), Path(c.__file__), Path(c.core.__file__), Path(c.old.__file__))},
                   "caveat": "Refinement differences are diagnostics, not certified error bounds. No pole location is certified."}
        (args.output / "results.json").write_text(json.dumps(payload, indent=2)+"\n")
        np.savez_compressed(args.output / "arrays.npz", **arrays)


if __name__ == "__main__":
    main()
