#!/usr/bin/env python3
"""Short accuracy refinement at L=0.6; reuse the saved independent monitor."""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

import compare_monodromy as c


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).parent / "results/contour_accuracy_refinement")
    args = parser.parse_args()
    baseline = Path(__file__).parent / "results/stress_continuation/arrays.npz"
    saved = np.load(baseline)
    grid = saved["grid_0.6"]
    reference = saved["reference_0.6"]
    jac = saved["jac_0.6_7.2"]
    middle = len(grid)//2
    bg = c.background(.6)
    fresh_reference, _ = c.rk_matrix(grid, bg, 3e-14, "DOP853")
    repeat_error = c.scaled_max(fresh_reference-reference, reference)
    if repeat_error > 1e-12:
        raise RuntimeError("Fresh reference does not reproduce the saved baseline")
    args.output.mkdir(parents=True, exist_ok=False)
    records, arrays = [], {}
    for radius in (5.4, 6.):
        for tol in (1e-12, 3e-13, 3e-14):
            print(f"R={radius}, tol={tol:g}", flush=True)
            matrix, cost = c.contour_matrix(grid, bg, radius, tol, balanced=True)
            record = {"radius": radius, "internal_tolerance": tol,
                      **cost, **c.summarize(matrix, reference, jac)}
            error = record["solution_error_vs_dop853"]
            amplification = record["variation_error_vs_dop853"] / error
            record["measured_error_amplification"] = amplification
            # This is a conditional extrapolation, not a computed contour solution.
            record["predicted_variation_error_at_solution_error_1e_minus_12"] = amplification*1e-12
            records.append(record)
            arrays[f"F_R{radius}_tol{tol}"] = matrix
            print(json.dumps(record), flush=True)
    # Componentwise max-norm bound for J E, in the norms used by summarize().
    bound = (np.max(np.sum(np.abs(jac), axis=2))*np.max(np.abs(reference))
             / np.max(np.abs(jac[middle])))
    payload = {
        "records": records, "reference_repeat_error": repeat_error,
        "monitor_drift_on_reference": c.summarize(reference, reference, jac)["monodromy_variation_drift"],
        "max_norm_amplification_bound_on_sampled_grid": float(bound),
        "numpy": np.__version__, "scipy": c.scipy.__version__,
        "hashes": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in (Path(__file__), Path(c.__file__), Path(c.core.__file__),
                             Path(c.old.__file__), baseline)},
        "caveat": "Predictions at 1e-12 scale the observed error direction; they are not achieved accuracies or guaranteed drift estimates. The reference and monitor have finite errors."}
    (args.output / "results.json").write_text(json.dumps(payload, indent=2)+"\n")
    np.savez_compressed(args.output / "arrays.npz", **arrays)


if __name__ == "__main__":
    main()
