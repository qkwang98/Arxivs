#!/usr/bin/env python3
"""Run the Lean axiom inventory and reject undeclared trust dependencies."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
result = subprocess.run(
    ["lake", "env", "lean", "Audit.lean"], cwd=root,
    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
(root / "validation").mkdir(exist_ok=True)
(root / "validation/AXIOMS.txt").write_text(result.stdout)
if result.returncode:
    print(result.stdout)
    raise SystemExit(result.returncode)

allowed = {"propext", "Classical.choice", "Quot.sound"}
observed = {
    axiom.strip()
    for block in re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout)
    for axiom in block.split(",") if axiom.strip()
}
expected_count = (root / "Audit.lean").read_text().count("#print axioms ")
actual_count = result.stdout.count("depends on axioms:") + result.stdout.count(
    "does not depend on any axioms"
)
if observed - allowed:
    raise SystemExit(f"Unexpected axiom dependencies: {sorted(observed - allowed)}")
if actual_count != expected_count:
    raise SystemExit(f"Missing audit results: expected {expected_count}, got {actual_count}")
print(f"Axiom inventory passed for {actual_count} public theorems.")
print(f"Observed foundational axioms: {', '.join(sorted(observed))}")
print("This checks axiom dependencies; visible theorem hypotheses still require proofs.")
