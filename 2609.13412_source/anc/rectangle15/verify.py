#!/usr/bin/env python3
"""Verify the order-15 rectangular proof, including coefficient regeneration.

Usage: python verify.py
Only the Python standard library is used. No solver, floating-point arithmetic,
old cone matrix, or untrusted binary cache is used by this program.
The mathematical positivity argument is in proof.md.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from math import factorial, gcd
from pathlib import Path
import json
from exact_algebra import (partitions, dimension, character, z, branching_row,
                           central_row, marked_cycle_counts)

ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def check_character_tables() -> None:
    for n in range(1, 16):
        ps = partitions(n)
        T = [[character(a, rho) for rho in ps] for a in ps]
        weights = [factorial(n)//z(rho) for rho in ps]
        for i, a in enumerate(ps):
            require(T[i][-1] == dimension(a), 'character degree mismatch')
            weighted = [x*w for x, w in zip(T[i], weights)]
            for j in range(i+1):
                require(sum(x*y for x, y in zip(weighted, T[j]))
                        == (factorial(n) if i == j else 0),
                        'character orthogonality failure')
    print('PASS: character degrees and exact orthogonality through order 15', flush=True)


def main() -> None:
    cert = json.loads((ROOT/'certificate.json').read_text())
    require(cert['order'] == 15 and cert['target'] == [3]*5, 'wrong theorem')
    ps = tuple(tuple(a) for a in cert['partitions'])
    require(ps == partitions(15) and len(ps) == 176, 'incomplete coordinate list')
    fs = [dimension(a) for a in ps]
    target = ps.index((3,)*5)
    require(fs[target] == 6006, 'wrong rectangular dimension')
    M = int(cert['scale'])
    require(M > 0, 'nonpositive certificate scale')
    terms = cert['terms']
    require(len(terms) == 125, 'unexpected number of terms')
    require(Counter(t['kind'] for t in terms) == {'central':106, 'branch':19},
            'unexpected witness counts')
    check_character_tables()
    by_group = defaultdict(list)
    computed = {}
    for i, term in enumerate(terms):
        require(term['id'] == i+1, 'term ordering mismatch')
        require(isinstance(term['weight'], str) and int(term['weight']) > 0,
                'nonpositive or noninteger weight')
        if term['kind'] == 'branch':
            computed[i] = branching_row(tuple(term['beta']), tuple(term['gamma']), ps)
        else:
            a, b, k = tuple(term['alpha']), tuple(term['beta']), term['swaps']
            by_group[sum(a), sum(b), k].append((i, a, b, k))
    print('PASS: all 19 branching rows regenerated from content differences', flush=True)
    rebuilt = 0
    for (p, q, k), group in sorted(by_group.items()):
        counts = marked_cycle_counts(p, q, k) if k > 1 else None
        for i, a, b, kk in group:
            computed[i] = central_row(a, b, kk, ps, counts)
        rebuilt += len(group)
        print(f'PASS: exact central rows ({p},{q}; k={k}): {len(group)}', flush=True)
    require(rebuilt == 106, 'wrong reconstruction count')
    total = [0]*len(ps)
    for i, term in enumerate(terms):
        row = computed[i]
        expected = {tuple(a):v for a, v in term['coefficients']}
        require(len(expected) == len(term['coefficients']), 'duplicate coefficient')
        require(expected == {a:v for a, v in zip(ps, row) if v},
                f'reconstructed coefficient mismatch at term {i+1}')
        require(gcd(*row) == 1, 'row is not primitive')
        require(sum(v*f for v, f in zip(row, fs)) == 0, 'unbalanced witness')
        w = int(term['weight'])
        total = [t+w*v for t, v in zip(total, row)]
    wanted = [0]*len(ps)
    wanted[0], wanted[target] = M*6006, -M
    require(total == wanted, 'final coefficient identity failed')
    require(gcd(M, *(int(t['weight']) for t in terms)) == 1,
            'common scale has a redundant factor')
    print('PASS: all 125 primitive rows, all positive integer weights, all balances', flush=True)
    print('PASS: all 176 coordinates of sum_i z_i R_i = M (6006 per - d_(3^5))', flush=True)
    # Diagnostic only: show a used branching inequality violates the old separator.
    dual = json.loads((ROOT/'old_separator.json').read_text())
    require(tuple(map(tuple,dual['partitions'])) == ps, 'separator coordinates differ')
    y = dual['dual_integer']
    j = 119
    require(terms[j]['beta'] == [4,4,4,1,1]
            and terms[j]['gamma'] == [4,4,3,1,1], 'diagnostic term changed')
    pair = sum(v*f*yy for v, f, yy in zip(computed[j], fs, y))
    require(pair == -116616500 and pair//50050 == -2330,
            'old-separator escape check failed')
    print('PASS: used branching term 120 has old-separator pairing -2330 after normalization', flush=True)
    print('ALL EXACT CHECKS PASSED.', flush=True)
    print('Mathematical consequence, by proof.md: per(A) >= d_(3^5)(A)/6006 for every complex PSD A.')


if __name__ == '__main__':
    main()
