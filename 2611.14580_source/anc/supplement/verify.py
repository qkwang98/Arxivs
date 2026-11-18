"""Run the arithmetic paper's six exact Python checks using only the stdlib.

Usage: python verify.py
Requires Python 3.10+; do not pass -O or -OO. Immutable inputs are verified
before and after execution. Every generated file is placed under reports/.
The three Singular scripts must be run separately as described in README.txt.
"""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time


def verify_hashes(root, manifest):
    mismatches = []
    for name, record in manifest['files'].items():
        path = root / name
        actual = sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        if actual != record['sha256']:
            mismatches.append({'file': name, 'expected': record['sha256'], 'actual': actual})
    return mismatches


def main():
    if not __debug__:
        raise SystemExit('Assertions are part of the checks; do not use -O or -OO.')
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    mismatches = verify_hashes(root, manifest)
    if mismatches:
        print(json.dumps({'status': 'FAIL', 'hash_mismatches': mismatches}, indent=2))
        return 1
    reports = root / 'reports'
    replay = reports / 'replay' / 'computations'
    replay.mkdir(parents=True, exist_ok=True)
    legacy_checks = [
        'linear-constants-check.py',
        'illustrated-strands-check.py',
        'koszul33-check.py',
        'goldbach-cutoff132-single-colon.py',
        'dual-koszul-cocycles-check.py',
    ]
    # Two original checkers write relative to __file__. Run unchanged copies
    # under reports/ so the immutable computational inputs stay untouched.
    for name in legacy_checks + ['illustrated-strands-data.json']:
        shutil.copyfile(root / 'computations' / name, replay / name)
    commands = [(name, [sys.executable, str(replay / name)]) for name in legacy_checks]
    commands.append(('prime-pair-depth-check.py', [
        sys.executable, str(root / 'computations' / 'prime-pair-depth-check.py'),
        '--output', str(reports / 'prime-pair-depth-verification.json'),
    ]))
    results = []
    start = time.monotonic()
    for name, command in commands:
        check_start = time.monotonic()
        result = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                encoding='utf-8', errors='replace')
        log = reports / (Path(name).stem + '.txt')
        log.write_text(result.stdout + result.stderr, encoding='utf-8')
        status = 'PASS' if result.returncode == 0 else 'FAIL'
        results.append({
            'check': name, 'status': status, 'exit_code': result.returncode,
            'elapsed_seconds': round(time.monotonic() - check_start, 3),
            'log': log.relative_to(root).as_posix(),
        })
        print(status + ' ' + name, flush=True)
        if result.returncode:
            print(result.stdout + result.stderr)
    mismatches = verify_hashes(root, manifest)
    passed = all(result['status'] == 'PASS' for result in results) and not mismatches
    report = {
        'status': 'PASS' if passed else 'FAIL',
        'timestamp_utc': datetime.now(timezone.utc).isoformat(),
        'python_version': sys.version.split()[0],
        'immutable_hashes_match_before_and_after': not mismatches,
        'checks': results,
        'singular_scripts_executed': False,
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'scope': 'Exact finite checks for the arithmetic paper. The six Python '
                 'checks run afresh. Hashes cover the three Singular scripts, '
                 'but they are not executed by this runner. General algebraic '
                 'and analytic theorems remain proved in the manuscript.',
    }
    if mismatches:
        report['hash_mismatches_after_execution'] = mismatches
    (reports / 'verification.json').write_text(json.dumps(report, indent=2) + '\n',
                                             encoding='utf-8')
    print('OVERALL ' + report['status'])
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
