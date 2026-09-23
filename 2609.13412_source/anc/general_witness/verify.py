#!/usr/bin/env python3
"""Check the finite certificates, polynomial identities, and cone separators.

Run: python verify.py
All arithmetic is exact; only the Python standard library is required.
The mathematical positivity proofs (not replaced by these checks) are in proof.md.
"""
from __future__ import annotations
import gzip
import json
from fractions import Fraction
from pathlib import Path
from core import *

ROOT = Path(__file__).resolve().parent

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)

def order15() -> None:
    cert = json.loads((ROOT/'certificate_order15.json').read_text())
    result: dict[Partition, int] = {}
    for term in cert['witnesses']:
        require(term['integer_multiplier'] > 0, 'nonpositive order-15 multiplier')
        row = witness(term['p'], tuple(term['beta']), term['k'])
        for nu, value in row.items():
            result[nu] = result.get(nu, 0)+term['integer_multiplier']*value
    result = {nu: x for nu, x in result.items() if x}
    expected = {tuple(t['partition']): t['coefficient']
                for t in cert['full_integer_identity']}
    require(result == expected, 'order-15 character-vector identity failed')
    lam = (5,4,3,3)
    normalizer = -result[lam]*dimension(lam)
    weights = {nu: Fraction(x*dimension(nu), normalizer)
               for nu, x in result.items() if x > 0}
    require(sum(weights.values()) == 1, 'order-15 weights do not sum to one')
    require(weights == {(9,3,3):Fraction(14,33), (8,4,3):Fraction(791,1485),
                        (7,5,3):Fraction(2,55), (7,4,4):Fraction(2,297)},
            'unexpected normalized order-15 weights')
    print('PASS: seven-witness order-15 identity and all four normalized weights')

def family() -> None:
    # Each combined-column identity is a polynomial in m of degree <= 3.
    # Four distinct exact checks therefore verify the polynomial identities.
    for m in range(6,10):
        multipliers = (9, 90*(m-3), 5*(m-3))
        total = tuple(sum(a*b for a,b in zip(row, multipliers))
                      for row in family_columns(m))
        require(total == family_coefficients(m), 'family polynomial identity failed')
    # Independent evaluations of the content/finite-difference definition.
    for m in range(6,19):
        rows = (witness(4,(m,3,3),3), witness(m,(4,3,3),1),
                witness(m+1,(3,3,3),2))
        for j, row in enumerate(rows):
            expected = {nu: col[j] for nu,col in zip(family_shapes(m),family_columns(m))
                        if col[j]}
            require(row == expected, 'content formula disagrees with family table')
    # Nonnegativity for all m>=6 is proved by the shifted polynomial
    # factorizations in proof.md.  The following also checks normalization.
    for m in range(6,101):
        shapes, coeff = family_shapes(m), family_coefficients(m)
        require(all(x >= 0 for x in coeff[:-1]) and coeff[-1] < 0,
                'invalid family coefficient signs')
        require(sum(x*dimension(nu) for nu,x in zip(shapes,coeff)) == 0,
                'family character-degree balance failed')
    print('PASS: degree-bounded polynomial identity, independent content checks, normalization')

def extras() -> None:
    directory = ROOT/'additional_certificates'
    if not directory.exists():
        return
    for file in sorted(directory.glob('*.json')):
        cert = json.loads(file.read_text()); n = cert['order']
        result: dict[Partition, Fraction] = {}
        for term in cert['witnesses']:
            alpha,beta,k = term['label']
            require(len(alpha) == 1, 'extra certificate is not symmetric-filter data')
            row = primitive_witness(alpha[0], tuple(beta), k)
            multiplier = Fraction(term['multiplier'])
            require(multiplier >= 0, 'negative witness multiplier')
            for nu,x in row.items():
                result[nu] = result.get(nu,Fraction())+multiplier*x*dimension(nu)
        result = {nu:x for nu,x in result.items() if x}
        expected = {tuple(t['partition']):Fraction(t['weight']) for t in cert['rhs']}
        expected[tuple(cert['target'])] = Fraction(-1)
        require(result == expected, f'extra certificate failed: {file.name}')
        require(all(Fraction(t['weight']) >= 0 for t in cert['rhs']), 'negative RHS weight')
        require(sum(Fraction(t['weight']) for t in cert['rhs']) == 1, 'RHS mass not one')
        print('PASS: additional exact certificate', n, tuple(cert['target']))

def nonsingular_mod(matrix: list[list[int]], prime: int) -> bool:
    a = [[x % prime for x in row] for row in matrix]
    for i in range(len(a)):
        pivot = next((j for j in range(i,len(a)) if a[j][i]), None)
        if pivot is None:
            return False
        a[i],a[pivot] = a[pivot],a[i]
        inv = pow(a[i][i],-1,prime)
        for j in range(i+1,len(a)):
            scale = a[j][i]*inv % prime
            if scale:
                a[j][i:] = [(x-scale*y)%prime for x,y in zip(a[j][i:],a[i][i:])]
    return True

def cones() -> None:
    for n in (14,15):
        with gzip.open(ROOT/f'cone_{n}.json.gz','rt') as file:
            data = json.load(file)
        parts = [tuple(v) for v in data['partitions']]
        degrees = [dimension(v) for v in parts]
        rows = data['primitive_rows']
        require(len(set(map(tuple,rows))) == len(rows), 'duplicate generator ray')
        require(all(sum(x*f for x,f in zip(row,degrees)) == 0 for row in rows),
                'a cone row is not balanced')
        rank = data['rank_certificate']
        minor = [[rows[i][j] for j in rank['pivot_columns']]
                 for i in rank['pivot_rows']]
        require(nonsingular_mod(minor,rank['prime']), 'modular rank certificate failed')
        require(len(minor) == len(parts)-1, 'incorrect rank bound')
        print('PASS: cone', n, 'rays',len(rows),'exact rank',len(minor))
        if n == 15:
            dual = json.loads((ROOT/'dual_15_33333.json').read_text())
            require(parts == [tuple(v) for v in dual['partitions']], 'dual order mismatch')
            y = dual['dual_integer']
            require(all(0 <= v <= 10000 for v in y), 'unexpected separator bounds')
            require(y[-1] == 0, 'separator does not annihilate determinant coordinate')
            margins = [sum(x*f*v for x,f,v in zip(row,degrees,y)) for row in rows]
            target_index = parts.index((3,3,3,3,3))
            gap = y[0]-y[target_index]
            require(all(v <= y[0] for i,v in enumerate(y) if i != target_index),
                    'separator is negative on another PDC ray')
            require(min(margins) == 98 and gap == -300, 'cone separation failed')
            print('PASS: exact order-15 separator, including every other PDC ray; gap =',Fraction(gap,dual['scale']))

if __name__ == '__main__':
    order15(); family(); extras(); cones()
    print('ALL CHECKS PASSED.  General positivity and all-parameter validity are proved in proof.md.')
