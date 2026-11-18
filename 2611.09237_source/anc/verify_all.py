#!/usr/bin/env python3
"""Reconstruct the bounded proof inputs. --extended adds finite Type A diagnostics."""
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
from time import perf_counter


def check_manifest(root):
    manifest = root / "CERTIFICATE_MANIFEST.sha256"
    if not manifest.is_file():
        raise RuntimeError("CERTIFICATE_MANIFEST.sha256 is missing from the ancillary files")
    checked = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, relative = line.split("  ", 1)
        path = (root / relative).resolve()
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            raise RuntimeError(f"Invalid or missing manifest entry: {relative}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"File identity mismatch: {relative}")
        checked += 1
    print(f"PASS manifest: {checked} file identities. This checks identity, not mathematical validity.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended", action="store_true", help="also run the S6/S7 and horizontal Type A diagnostics")
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        raise RuntimeError("Python 3.10 or later is required")
    if not __debug__:
        raise RuntimeError("Run without -O: the optional Type A diagnostics use assertions")
    here = Path(__file__).resolve().parent
    started = perf_counter()
    check_manifest(here)
    tasks = [("verify_torsion_certificates.py", "--verify-only", "--check-stored"),
             ("verify_root_permutations.py",), ("verify_type_d.py",)]
    if args.extended:
        tasks.extend([("check_type_a.py", "6"), ("check_type_a.py", "7"),
                      ("check_type_a_auxiliary.py", "6")])
    for index, task in enumerate(tasks, 1):
        print("Running " + " ".join(task), flush=True)
        task_started = perf_counter()
        subprocess.run([sys.executable, "-I", "-B", str(here / task[0]), *task[1:]], check=True)
        print(f"Elapsed task time: {' '.join(task)}: "
              f"{perf_counter() - task_started:.6f} seconds.", flush=True)
        if index == 3:
            print(f"DEFAULT CHECKS PASSED ({perf_counter() - started:.6f} seconds).", flush=True)
    print(f"Total elapsed time: {perf_counter() - started:.6f} seconds.", flush=True)
    print("ALL REQUESTED CHECKS PASSED.", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
