"""Exact finite dual Koszul cocycles in the binary Goldbach ring.

Python standard library only. Reconstructs binary-move components over Z,
checks signed differentials, and uses an integral coefficient functional
which vanishes on every incoming column and takes the cocycle to 1.
No equality with the toric quotient and no characteristic-zero inference
is used. The checked supports are every odd-prime prefix through 101,
starting with {3,5,7,11}; the separate cutoff-8 example is also checked.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
from math import prod
from pathlib import Path
import json


def primes_to(bound):
    return tuple(p for p in range(3, bound + 1, 2)
                 if all(p % q for q in range(2, int(p ** .5) + 1)))


class BinaryRing:
    def __init__(self, support):
        self.support = tuple(support)
        self.pairs = {}
        for pair in combinations_with_replacement(self.support, 2):
            self.pairs.setdefault(sum(pair), []).append(pair)

    @lru_cache(None)
    def components(self, degree):
        """Canonical monomial in every actual binary-move component."""
        vertices = tuple(combinations_with_replacement(self.support, degree))
        parent = {v: v for v in vertices}

        def find(v):
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v

        for v in vertices:
            for i, j in combinations(range(degree), 2):
                rest = v[:i] + v[i+1:j] + v[j+1:]
                for pair in self.pairs[v[i] + v[j]]:
                    w = tuple(sorted(rest + pair))
                    assert sum(w) == sum(v) and len(w) == len(v)
                    a, b = find(v), find(w)
                    if a != b:
                        parent[a] = b
        groups = {}
        for v in vertices:
            groups.setdefault(find(v), []).append(v)
        normal = {}
        for group in groups.values():
            rep = max(group, key=lambda v: (prod(v), v))
            for v in group:
                normal[v] = rep
        return normal

    def normalize(self, terms):
        out = Counter()
        for coefficient, monomial, exterior in terms:
            assert tuple(sorted(exterior)) == tuple(exterior)
            assert len(set(exterior)) == len(exterior)
            monomial = tuple(sorted(monomial))
            rep = self.components(len(monomial))[monomial]
            out[tuple(exterior), rep] += coefficient
        return {key: value for key, value in out.items() if value}

    def delta(self, terms):
        result = []
        for coefficient, monomial, exterior in terms:
            for p in self.support:
                if p not in exterior:
                    sign = (-1) ** sum(q < p for q in exterior)
                    result.append((coefficient * sign,
                                   tuple(sorted(tuple(monomial) + (p,))),
                                   tuple(sorted(tuple(exterior) + (p,)))))
        return self.normalize(result)


def check_small_example():
    ring = BinaryRing((3, 5, 7))
    z = [(1, (3,), (3, 5)), (1, (5,), (3, 7))]
    assert not ring.delta(z)
    # In internal bidegree (-5,-1), C1 consists only of the basis epsilon_5.
    incoming = [(1, (), (5,))]
    detector = ((3, 7), (5,))
    assert ring.normalize(z)[detector] == 1
    assert ring.delta(incoming).get(detector, 0) == 0
    return {'cutoff': 8, 'internal_bidegree': [-5, -1],
            'closed': True, 'integral_nonboundary_detector': True}


def main():
    if not __debug__:
        raise SystemExit('Assertions are part of the certificate; do not use -O/-OO.')
    all_primes = primes_to(101)
    choices = {5: (3, 3), 7: (3, 5)}
    cases = []
    identity_count = 0
    for last in all_primes[3:]:
        ring = BinaryRing(tuple(p for p in all_primes if p <= last))
        representations = ring.pairs[last + 1]
        choices[last] = max(representations, key=prod)
        assert all(sum(mon) == p + 1 and len(mon) == 2
                   for p, mon in choices.items())
        # All quadratic representations already coincide by a single binary
        # move. The cubic tests below, in contrast, require actual paths.
        normal2 = ring.components(2)
        for p, mon in choices.items():
            assert all(normal2[pair] == normal2[mon]
                       for pair in ring.pairs[p + 1])
        normal3 = ring.components(3)
        for p, q in combinations(choices, 2):
            left = tuple(sorted((p,) + choices[q]))
            right = tuple(sorted((q,) + choices[p]))
            assert normal3[left] == normal3[right], (last, p, q, left, right)
            identity_count += 1
        z = [(1, mon, (3, p)) for p, mon in choices.items()]
        assert all(sum(mon) - sum(ext) == -2 and len(mon) - len(ext) == 0
                   for _, mon, ext in z)
        assert not ring.delta(z), ('Signed cocycle check failed', last)
        detector = ((3, 11), (5, 7))
        assert ring.normalize(z)[detector] == 1
        # Enumerate the entire incoming C1 basis in bidegree (-2,0).
        # A coefficient at epsilon_p must be x_(p-2). Neither p=3 nor
        # p=11 admits such a variable, so this functional kills all boundaries.
        incoming_columns = 0
        for p in ring.support:
            if p - 2 in ring.support:
                column = ring.delta([(1, (p - 2,), (p,))])
                assert column.get(detector, 0) == 0
                incoming_columns += 1
        assert 1 not in ring.support and 9 not in ring.support
        cases.append({'cutoff': last + 1, 'support': ring.support,
                      'terms': len(z), 'cubic_identities': len(choices)*(len(choices)-1)//2,
                      'incoming_columns': incoming_columns,
                      'closed_over_every_field': True,
                      'nonboundary_over_every_field': True})
    assert len(cases) == 22 and identity_count == 2299
    report = {
        'status': 'PASS', 'coefficient_fields': 'Every field',
        'method': 'Integral binary-move components, signed exterior differential, '
                  'and coefficient functional with value 1 on the cocycle '
                  'and value 0 on every incoming basis column.',
        'formula': 'omega_m = epsilon_3 wedge sum_(5<=q<m) y_q epsilon_q',
        'codifferential': 'd^star(omega) = theta_m wedge omega',
        'representative_choice': 'For q+1=p_1+p_2, choose x_(p_1)*x_(p_2) '
                                 'with maximum product p_1*p_2; y_q is its class.',
        'internal_bidegree': [-2, 0],
        'supports_checked': len(cases), 'cubic_identities_checked': identity_count,
        'coefficients': [{'q': q, 'y_q': mon} for q, mon in choices.items()],
        'small_example': check_small_example(), 'cases': cases,
        'scope': 'Every distinct odd-prime support for integers 12<=m<=102, '
                 'plus the separate cutoff-8 example. No infinite-family '
                 'claim and no full-depth or full-cohomology calculation.'}
    path = Path(__file__).resolve().parent.parent / 'reports' / 'dual-koszul-cocycles-verification.json'
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('PASS: 22 odd-prime prefixes, last primes 11 through 101')
    print('PASS: 2299 cubic binary-connectivity identities and signed cocycle checks')
    print('PASS: integral nonboundary detectors for every prefix and cutoff 8')
    print('Field scope: every field; no characteristic-zero extrapolation')
    print('Infinite extension remains conjectural')


if __name__ == '__main__':
    main()
