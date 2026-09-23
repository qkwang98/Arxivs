#!/usr/bin/env python3
"""Verify generated sources without modifying this project. Not a proof checker."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
jobs = [
    ("generate_certificate.py", "CertificateData.lean"),
    ("generate_certificate_checks.py", "CertificateChecks.lean"),
]
with tempfile.TemporaryDirectory(prefix="lieb-certificate-") as name:
    scratch = Path(name)
    (scratch / "Bridge").mkdir()
    (scratch / "scripts").mkdir()
    (scratch / "specification/exact_certificate").mkdir(parents=True)
    shutil.copy2(
        root / "specification/exact_certificate/certificate.json",
        scratch / "specification/exact_certificate/certificate.json",
    )
    for generator, target in jobs:
        script = scratch / "scripts" / generator
        shutil.copy2(root / "scripts" / generator, script)
        subprocess.run([sys.executable, str(script)], cwd=scratch, check=True)
        if (scratch / "Bridge" / target).read_bytes() != (root / "Bridge" / target).read_bytes():
            raise SystemExit(f"Generated source mismatch: {target}")
        print(f"Exact generated-source match: {target}")
