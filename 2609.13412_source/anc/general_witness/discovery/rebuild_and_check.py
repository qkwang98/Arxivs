#!/usr/bin/env python3
"""Regenerate central-projector cones and compare all rays with the release data.

Requires NumPy and SciPy.  Representation-theoretic arithmetic uses Python
integers (NumPy dtype=object); no numerical LP is used by this command.
The cache is generated locally. Do not use pickle cache files from untrusted
sources. A fresh cache forces a from-scratch computation.
"""
from __future__ import annotations
import argparse
import gzip
import json
import sys
from pathlib import Path
import research
import contractions
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from core import primitive_witness


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('orders', nargs='*', type=int, default=[14,15])
    parser.add_argument('--cache-dir', type=Path,
                        default=Path(__file__).resolve().parent/'cache')
    args = parser.parse_args()
    args.cache_dir.mkdir(parents=True, exist_ok=True)
    research.ROOT = contractions.ROOT = args.cache_dir.resolve()
    bundle = Path(__file__).resolve().parent.parent
    for n in args.orders:
        path = bundle/f'cone_{n}.json.gz'
        if not path.exists():
            raise ValueError(f'No released reference matrix for order {n}')
        with gzip.open(path,'rt') as file:
            reference = json.load(file)
        calculated = contractions.full_data(n)
        if calculated['parts'] != tuple(tuple(v) for v in reference['partitions']):
            raise ArithmeticError('Partition ordering mismatch')
        got = set(calculated['rows'])
        expected = set(map(tuple,reference['primitive_rows']))
        if got != expected:
            raise ArithmeticError(f'Ray-set mismatch: missing={len(expected-got)}, '
                                  f'additional={len(got-expected)}')
        labels = 0
        for p in range(1,n//2+1):
            q=n-p
            a,b=len(research.partitions(p)),len(research.partitions(q))
            labels += p*(a*b if p!=q else a*(a+1)//2)
        zero = labels-len(calculated['bylabel'])
        if (labels,zero) != (reference['parameter_labels'],reference['zero_labels']):
            raise ArithmeticError('Parameter-count mismatch')
        checked = 0
        for (a,b,k),row in calculated['bylabel'].items():
            if len(a) != 1:
                continue
            content = primitive_witness(a[0],b,k)
            predicted = tuple(content.get(nu,0) for nu in calculated['parts'])
            if row != predicted:
                raise ArithmeticError(f'Independent content check failed: {a,b,k}')
            checked += 1
        print(f'PASS: independent content checks for {checked} symmetric-first-block labels')
        print(f'PASS: regenerated order {n}; {labels} labels, {zero} zeros, '
              f'{len(got)} distinct rays',flush=True)

if __name__=='__main__':
    main()
