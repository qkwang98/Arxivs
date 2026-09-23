"""Rebuild the six English tables from the distributed numerical records."""
import argparse
import json
from pathlib import Path
import subprocess
import sys


def sci(value):
    mantissa, exponent = f"{float(value):.3e}".split("e")
    return rf"${mantissa}\cdot10^{{{int(exponent)}}}$"


def tabular(rows, spec, headings):
    return (r"\begin{tabular}{" + spec + "}\n\\toprule\n" + headings
            + "\\\\\n\\midrule\n" + "\n".join(rows)
            + "\n\\bottomrule\n\\end{tabular}\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("tables_rebuilt"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent / "computational_preprint"
    if not root.exists():
        root = Path(__file__).resolve().parents[1]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)

    def data(name):
        return json.loads((root / "results" / name / "results.json").read_text())

    pii = data("pii_comparison")
    rows = []
    for level, (key, pair) in enumerate(pii["pairs"].items(), 1):
        assert pair["matched"]
        for label, record in [("Contour", pii["contours"][key]),
                              ("RK", pii["rk_trials"][pair["rk_tolerance"]])]:
            rows.append(f"{level} & {label} & " + " & ".join(sci(record[k]) for k in
                        ["max_solution_error", "max_variation_drift", "max_wronskian_error"])
                        + f" & {record['seconds']:.2f}" + r"\\")
    heading = r"Level & Method & $E$ & $D$ & $W_{\rm err}$ & Time (s)"
    (output / "pii.tex").write_text(tabular(rows, "clrrrr", heading))
    rows = []
    for level, name in enumerate(["equal_accuracy_coarse_matched", "equal_accuracy_fine"], 1):
        record = data(name)
        key = next(iter(record["pairs"]))
        pair = record["pairs"][key]
        assert pair["matched"]
        for label, result in [("Contour", record["contours"][key]),
                              ("RK", record["rk_trials"][pair["rk_tolerance"]])]:
            seconds = result["standalone_seconds"] if label == "Contour" else result["seconds"]
            rows.append(f"{level} & {label} & " + " & ".join(sci(result[k]) for k in
                        ["max_solution_error", "max_variation_drift", "max_wronskian_error"])
                        + f" & {seconds:.2f}" + r"\\")
    (output / "piv.tex").write_text(tabular(rows, "clrrrr", heading))
    transition = data("rigid_oscillatory_checked_e02")
    controls = data("rigid_oscillatory_controls")
    assert transition["status"] == controls["status"] == "complete"
    matched = transition["rk_trials"][transition["matched_pair"]["rk_tolerance"]]
    records = [("Contour", transition["contour"]),
               (r"RK, $\tau=10^{-12}$", transition["rk_trials"]["1.0e-12"]),
               ("RK, matched", matched), ("RK, variable tolerance", controls["rk_tightened"])]
    rows = [label + " & " + sci(rec["max_solution_error"]) + " & "
            + sci(rec["max_row_variation_drift"]) + " & "
            + sci(rec["post_drift"]["max_row_drift"]) + r"\\" for label, rec in records]
    (output / "transition.tex").write_text(tabular(rows, "lrrr",
        r"Method & $E$ & $\max D_0$ & $\max D_{\rm osc}$"))
    rows = []
    for contour, rk in zip(transition["contour"]["post_drift"]["points"][1:],
                           matched["post_drift"]["points"][1:]):
        rows.append(f"{contour['t']:.6f} & " + sci(contour["max_row_drift"]) + " & "
                    + sci(rk["max_row_drift"]) + r"\\")
    (output / "late_drift.tex").write_text(tabular(rows, "rrr",
        r"$t$ & $D_{\rm osc}$, contour & $D_{\rm osc}$, RK"))
    subprocess.run([sys.executable, str(root / "build_parameter_report.py"),
                    "--tables", str(output)], check=True)
    for name in ["parameters.tex", "budget.tex"]:
        path = output / name
        text = path.read_text().replace("Данные", "Data").replace("Уточнение", "Refined")
        path.write_text(text)
    print(f"Six English tables written to {output}")


if __name__ == "__main__":
    main()
