#!/usr/bin/env python3
"""Clean project-source build using the existing pinned dependency cache.

Usage: python3 scripts/rebuild_isolated.py NEW_DIRECTORY
The destination must not exist. Original sources and build outputs are untouched.
This is build orchestration, not a proof checker.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
if len(sys.argv) != 2:
    raise SystemExit(__doc__)
dest = Path(sys.argv[1]).resolve()
if not (root / '.lake/packages').is_dir():
    raise SystemExit('Pinned dependency packages are missing; obtain them first.')
dest.mkdir(parents=True, exist_ok=False)
sources = list((root / 'Bridge').rglob('*.lean')) + [root / name for name in (
    'Bridge.lean', 'CompleteAudit.lean', 'Audit.lean', 'lakefile.toml',
    'lake-manifest.json', 'lean-toolchain')]
manifest = {}
for source in sources:
    relative = source.relative_to(root)
    target = dest / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
    manifest[str(relative)] = hashlib.sha256(source.read_bytes()).hexdigest()
(dest / 'SOURCE_SHA256.json').write_text(json.dumps(manifest, indent=2) + '\n')
(dest / '.lake').mkdir()
(dest / '.lake/packages').symlink_to(root / '.lake/packages', target_is_directory=True)
for command, log in [
    (['lake', 'build', 'Bridge', 'Bridge.Young'], 'BUILD.log'),
    (['lake', 'env', 'lean', 'CompleteAudit.lean'], 'AXIOMS.txt'),
]:
    print('Running ' + ' '.join(command), flush=True)
    with (dest / log).open('w') as output:
        subprocess.run(command, cwd=dest, stdout=output,
                       stderr=subprocess.STDOUT, check=True)
for relative, expected in manifest.items():
    for base in (root, dest):
        if hashlib.sha256((base / relative).read_bytes()).hexdigest() != expected:
            raise SystemExit(f'Source changed during build: {base / relative}')
print(f'Clean project build and axiom audit passed: {dest}')
print('Dependencies reused from the pinned cache; no project build outputs reused.')
