#!/usr/bin/env python3
"""Exact arithmetic for A Counterexample to the Huneke--Wiegand Conjecture.

Run with Python 3.10+; no third-party packages, external data, or network needed.
Every infinite relative-ideal equality is checked using all residue minima.
The algebraic interpretation of these integer certificates is proved in main.tex.
A failed check raises an exception and exits with a nonzero status, also under -O.
"""
from __future__ import annotations
import heapq
import json
from math import gcd
from functools import reduce

G = (56, 57, 58, 63, 64, 70, 71, 72, 73, 74, 75, 76, 77,
     78, 79, 80, 81, 82, 83, 87, 89, 90, 93, 95, 96, 97)
M = min(G)
Vector = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def apery(generators: tuple[int, ...]) -> Vector:
    require(bool(generators) and min(generators) > 0, 'Positive generators required.')
    require(reduce(gcd, generators) == 1, 'A numerical semigroup is required.')
    m = min(generators)
    distances: list[int | None] = [None] * m
    distances[0] = 0
    queue = [(0, 0)]
    while queue:
        distance, residue = heapq.heappop(queue)
        if distance != distances[residue]:
            continue
        for generator in generators:
            new_distance = distance + generator
            new_residue = new_distance % m
            old = distances[new_residue]
            if old is None or new_distance < old:
                distances[new_residue] = new_distance
                heapq.heappush(queue, (new_distance, new_residue))
    require(all(x is not None for x in distances), 'Some residue classes were not reached.')
    return tuple(int(x) for x in distances if x is not None)


def contains(vector: Vector, n: int) -> bool:
    return n >= vector[n % len(vector)]


def shift(vector: Vector, amount: int) -> Vector:
    m = len(vector)
    return tuple(amount + vector[(r - amount) % m] for r in range(m))


def union(*vectors: Vector) -> Vector:
    return tuple(min(xs) for xs in zip(*vectors))


def intersection(*vectors: Vector) -> Vector:
    return tuple(max(xs) for xs in zip(*vectors))


def ideal_sum(left: Vector, right: Vector) -> Vector:
    """Minkowski sum: supports of products of monomial ideals."""
    m = len(left)
    return tuple(min(left[s] + right[(r - s) % m] for s in range(m))
                 for r in range(m))


def generated(generators: tuple[int, ...], ring: Vector) -> Vector:
    return union(*(shift(ring, g) for g in generators))


def difference(left: Vector, right: Vector) -> list[int]:
    """The exact finite set left minus right, from all residue minima."""
    m = len(left)
    return sorted(n for r in range(m) for n in range(left[r], right[r], m))


def minimal_generators(ideal: Vector) -> list[int]:
    # Every minimal generator is in the relative Apery set: otherwise subtract M.
    return sorted(n for n in ideal if not any(contains(ideal, n - g) for g in G))



def interval(a: int, b: int) -> set[int]:
    return set(range(a, b + 1))


def main() -> None:
    gamma = apery(G)
    f = max(gamma) - M
    c = f + 1
    require(f == 181 and c == 182, 'Frobenius/conductor mismatch.')
    require(len(G) == 26 and len(set(G)) == 26, 'Generator count mismatch.')
    require(all(M <= g < 2 * M for g in G), 'Generator minimality failed.')
    gaps = [n for n in range(f + 1) if not contains(gamma, n)]
    gaps_expected = (interval(1, 55) | interval(59, 62) | interval(65, 69)
        | interval(84, 86) | {88} | interval(91, 92) | {94}
        | interval(98, 111) | interval(117, 118) | interval(123, 125) | {181})
    require(set(gaps) == gaps_expected and len(gaps) == 91, 'Gap list failed.')
    require(all(contains(gamma, n) != contains(gamma, f - n)
                for n in range(f + 1)), 'Symmetry failed.')
    require([n for n in gaps if all(contains(gamma, n + g) for g in G)] == [181],
            'Pseudo-Frobenius set failed.')
    membership_expected = ({0} | interval(56, 58) | interval(63, 64)
        | interval(70, 83) | {87} | interval(89, 90) | {93}
        | interval(95, 97) | interval(112, 116) | interval(119, 122)
        | interval(126, 180))
    require({n for n in range(182) if contains(gamma, n)} == membership_expected,
            'Semigroup interval list failed.')
    twoG = {a + b for a in G for b in G}
    require({n for n in twoG if n <= 181} == (
        interval(112, 116) | interval(119, 122) | interval(126, 180)),
        'Two-generator-sum interval identity failed.')
    require(interval(224, 279) <= {a + b for a in twoG for b in twoG},
            'Fourth-power block certificate failed.')
    require(all(contains(gamma, n) for n in range(c, c + M)),
            'Conductor-block certificate failed.')

    # Separately generated DP table checks the shortest-path implementation.
    bound = 1024
    dynamic = [False] * (bound + 1)
    dynamic[0] = True
    for n in range(1, bound + 1):
        dynamic[n] = any(g <= n and dynamic[n - g] for g in G)
    require(all(dynamic[n] == contains(gamma, n) for n in range(bound + 1)),
            'Independent membership implementations disagree.')

    B = (56, 57, 58, 63, 64, 73, 75, 76, 79, 81, 82, 83)
    C = interval(112, 116) | interval(119, 122) | interval(126, 152) | interval(154, 166)
    X = {n + 14 for n in C}
    E = intersection(gamma, shift(gamma, -14))
    D = intersection(gamma, shift(gamma, -14), shift(gamma, -28))
    require(E == generated(B, gamma), 'E = B + Gamma failed.')
    require(minimal_generators(E) == list(B), 'Minimal E generators failed.')
    require({a + b for a in B for b in B} == C, 'B + B = C failed.')
    require(len(C) == 49, 'C has the wrong size.')
    require(minimal_generators(D) == sorted(C), 'Minimal D generators failed.')
    require(D == generated(tuple(sorted(C)), gamma), 'D = C + Gamma failed.')
    require(ideal_sum(E, E) == D, 'Inverse-ideal equality failed.')
    Q = shift(E, 14)
    require(intersection(E, Q) == generated(tuple(sorted(X)), gamma),
            'Intersection support certificate failed.')
    require(intersection(E, Q) == ideal_sum(E, Q), 'Colon equality failed.')

    E_intervals = (set(B) | interval(112,116) | interval(119,122)
                  | interval(126,166) | interval(168,180))
    require({n for n in range(c) if contains(E, n)} == E_intervals,
            'E interval list failed.')
    require(all(contains(E, n) for n in range(c, c + M)), 'E tail failed.')
    require({b + g for b in B for g in G} == (
        interval(112,116) | interval(119,122) | interval(126,166)
        | interval(168,180)), 'B+G identity failed.')
    require({x + g for x in X for g in G} == (
        interval(182,194) | interval(196,277)), 'X+G identity failed.')

    # Nonprincipality and Hilbert--Samuel multiplicity certificate.
    J = union(gamma, shift(gamma, 14))
    require(minimal_generators(J) == [0,14], 'J is not minimally two generated.')
    require(not contains(gamma,14), 'The valuation obstruction is absent.')
    maximal = generated(G, gamma)
    power = gamma
    for _ in range(4):
        power = ideal_sum(power, maximal)
    fourth_expected = generated(tuple(range(224,280)), gamma)
    require(power == fourth_expected, 'Fourth power of the maximal ideal failed.')
    require(ideal_sum(power, maximal) == shift(power, 56), 'Reduction equality failed.')
    require(len(difference(gamma, shift(gamma,56))) == 56, 'Parameter colength failed.')

    # Trace and evaluation-image arithmetic.
    trace = union(E, Q)
    tgens = tuple(g for g in G if g not in (74,80))
    require(set(B) | {b+14 for b in B} == set(tgens), 'Trace generator union failed.')
    require(trace == generated(tgens, gamma), 'Trace ideal failed.')
    require(minimal_generators(trace) == list(tgens), 'Trace minimality failed.')
    require(difference(gamma, trace) == [0,74,80], 'Trace quotient basis failed.')
    require(not difference(trace, gamma), 'Trace not contained in ring.')

    # (J:J), computed from both monomial generators of J.
    end = intersection(J, shift(J,-14))
    end_Rgens = (0,101,107)
    require(end == generated(end_Rgens,gamma), 'Endomorphism module failed.')
    require(difference(end, gamma) == [101,107,181], 'End/R basis failed.')
    require(not difference(gamma,end), 'R not contained in End.')
    require(ideal_sum(end,end) == end, 'Endomorphism ring is not multiplicatively closed.')
    end_conductor = intersection(gamma, shift(gamma,-101), shift(gamma,-107))
    require(end_conductor == trace, 'Endomorphism conductor differs from trace.')
    require(difference(J,gamma) == [14,84,85,86,88,91,92,94,101,103,104,107,109,110,111,181],
            'J/R intermediate list failed.')

    # Quotient lengths and Artinian socles for the Tor corollary.
    p_missing = difference(gamma,E)
    q_missing = difference(gamma,Q)
    p_expected = [0,70,71,72,74,77,78,80,87,89,90,93,95,96,97,167]
    q_expected = sorted({0,56,57,58,63,64,73,74,75,76,79,80,81,82,83}
        | interval(112,116) | interval(119,122) | {131,132,137,138,139,195})
    require(p_missing == p_expected and len(p_missing) == 16, 'R/P basis failed.')
    require(q_missing == q_expected and len(q_missing) == 30, 'R/Q basis failed.')
    p_socle = [n for n in p_missing if all(contains(E,n+g) for g in G)]
    q_socle = [n for n in q_missing if all(contains(Q,n+g) for g in G)]
    require(p_socle == [167] and q_socle == [195], 'Quotient socles failed.')

    result = {
        'status': 'PASS',
        'method': 'Exact relative Apery vectors; no heuristic truncation.',
        'generators': list(G),
        'apery_mod_56': list(gamma),
        'multiplicity': 56, 'embedding_dimension': 26,
        'frobenius': f, 'conductor': c, 'genus': len(gaps),
        'symmetric': True, 'pseudo_frobenius_set': [181],
        'gap_set': gaps,
        'independent_DP_crosscheck_through': bound,
        'B': list(B), 'C': sorted(C), 'B_plus_B_equals_C': True,
        'colon_intersection_equals_product': True,
        'inverse_square_identity': True,
        'maximal_ideal_reduction_identity': 'm^5 = t^56 m^4',
        'dual_minimal_generators': 12,
        'trace_minimal_generator_exponents': list(tgens),
        'trace_colength': 3, 'trace_quotient_basis': [0,74,80],
        'endomorphism_R_module_generator_exponents': list(end_Rgens),
        'endomorphism_quotient_basis': [101,107,181],
        'endomorphism_quotient_length': 3,
        'trace_equals_endomorphism_conductor': True,
        'P_colength':16, 'Q_colength':30,
        'P_quotient_basis':p_missing, 'Q_quotient_basis':q_missing,
        'P_quotient_socle':[167], 'Q_quotient_socle':[195],
        'algebraic_scope': 'Integer certificates; see the paper for algebraic proofs.'
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
