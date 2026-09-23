#!/usr/bin/env python3
"""Run every exact local check in the certificate bundle."""
from pathlib import Path
import subprocess
import sys

def main():
    root=Path(__file__).resolve().parent
    for name in ('operator_identity_checks.py','verify_certificate.py','adversarial_exact_checks.py'):
        print('\n=== '+name+' ===',flush=True)
        subprocess.run([sys.executable,str(root/name)],cwd=root,check=True)
    print('\nALL EXACT CHECKS PASSED.\nAnalytic PSD positivity is proved in PROOF.md; no formal-kernel claim.',flush=True)

if __name__=='__main__':main()
