#!/usr/bin/env python3
"""Check selected Bridge modules using this project's pinned Lake environment.

Example:
  python3 scripts/check_module.py CertificateAlgorithm CertificateData \
      CertificateEnumeration CertificateChecks Certificate CertificateAxiomAudit
"""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
for name in sys.argv[1:]:
    target = root / '.lake/build/lib/lean/Bridge' / (name + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    source = root / 'Bridge' / (name + '.lean')
    print('Checking', name, flush=True)
    subprocess.run(['lake', 'env', 'lean', '-o', str(target), str(source)],
                   cwd=root, check=True)
