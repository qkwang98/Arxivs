#!/usr/bin/env python3
"""Inspect every project theorem's transitive axioms through Lean itself.

This is a read-only audit, not a proof-producing or certificate evaluation tool.
Run `lake build Bridge.Young` first; no sources or existing audits are changed.
"""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
result = subprocess.run(
    ["lake", "env", "lean", "CompleteAudit.lean"], cwd=root,
    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
out = root / "validation" / "complete"
out.mkdir(parents=True, exist_ok=True)
(out / "AXIOMS.txt").write_text(result.stdout)
if result.returncode:
    print(result.stdout)
    raise SystemExit(result.returncode)
match = re.search(r"AUDIT_CHECKED (\d+) project theorems", result.stdout)
if not match or int(match.group(1)) <= 100:
    raise SystemExit("Incomplete theorem inventory")
entries = re.findall(r"AXIOMS ([^:]+): \[([^\]]*)\]", result.stdout)
if len(entries) != int(match.group(1)):
    raise SystemExit("Audit entry count mismatch")
observed = {a.strip() for _, values in entries for a in values.split(",") if a.strip()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
if observed - allowed:
    raise SystemExit(f"Unexpected transitive axioms: {sorted(observed - allowed)}")
for endpoint in ("bridge_inequality", "normalized_bridge", "pdc4433_of_four_pate"):
    name = "LiebBridge.Young.FinalBridge." + endpoint
    if name not in {n for n, _ in entries}:
        raise SystemExit(f"Missing endpoint: {name}")
print(f"Passed: all {match.group(1)} imported project theorems.")
print("Complete axiom union: " + ", ".join(sorted(observed)))
print("Pate statements are four explicit theorem parameters, not global axioms.")
print("Full inventory and endpoint types: validation/complete/AXIOMS.txt")
