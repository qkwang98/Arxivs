#!/usr/bin/env python3
"""Check the finite certificates using explicit Euclidean root permutations.

This verifier does not import the Cartan-matrix reconstructor. It builds each
Weyl group by reflecting a concrete root set, independently checks Coxeter
length by inverted positive roots, recomputes every deletion centre and every
stored character witness, and evaluates determinants by the Leibniz formula.
Python 3.10+; standard library only; no files are modified.
"""

import argparse
from collections import Counter
from itertools import permutations, product
import json
from math import gcd, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def unit(n, i, scale=1):
    return tuple(scale if j == i else 0 for j in range(n))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def classical_roots(n, long_scale):
    roots = {unit(n, i, sign * long_scale) for i in range(n) for sign in (-1, 1)}
    for i in range(n):
        for j in range(i + 1, n):
            for a, b in product((-1, 1), repeat=2):
                roots.add(add(unit(n, i, a), unit(n, j, b)))
    return roots


def coordinates(kind, v):
    if kind == "A3":
        return tuple(sum(v[:i + 1]) for i in range(3))
    if kind.startswith("B"):
        return tuple(sum(v[:i + 1]) for i in range(len(v)))
    if kind.startswith("C"):
        require(sum(v) % 2 == 0, "A C root is outside its root lattice")
        return tuple(sum(v[:i + 1]) for i in range(len(v) - 1)) + (sum(v) // 2,)
    if kind == "F4":
        numerators = (v[0] + v[1], 2*v[0] + v[1] + v[2],
                      3*v[0] + v[1] + v[2] + v[3])
        require(all(x % 2 == 0 for x in numerators), "Nonintegral F4 root coordinate")
        return tuple(x // 2 for x in numerators) + (v[0],)
    if kind == "G2":
        return (v[2], v[2] - v[1])
    raise RuntimeError("Unknown root system")


def root_system(kind):
    if kind in ("B3", "C3", "C2"):
        n = int(kind[-1]); scale = 1 if kind[0] == "B" else 2
        roots = classical_roots(n, scale)
        simple = [add(unit(n, i), unit(n, i + 1, -1)) for i in range(n - 1)]
        simple.append(unit(n, n - 1, scale))
    elif kind == "A3":
        roots = {add(unit(4, i), unit(4, j, -1)) for i in range(4) for j in range(4) if i != j}
        simple = [add(unit(4, i), unit(4, i + 1, -1)) for i in range(3)]
    elif kind == "F4":
        # All Euclidean coordinates are doubled, including the half-integral roots.
        roots = {unit(4, i, 2*s) for i in range(4) for s in (-1, 1)}
        for i in range(4):
            for j in range(i + 1, 4):
                for a, b in product((-2, 2), repeat=2):
                    roots.add(add(unit(4, i, a), unit(4, j, b)))
        roots.update(product((-1, 1), repeat=4))
        simple = [(0, 2, -2, 0), (0, 0, 2, -2), (0, 0, 0, 2), (1, -1, -1, -1)]
    elif kind == "G2":
        roots = {add(unit(3, i), unit(3, j, -1)) for i in range(3) for j in range(3) if i != j}
        for i in range(3):
            v = tuple(2 if j == i else -1 for j in range(3))
            roots.add(v); roots.add(tuple(-x for x in v))
        simple = [(-2, 1, 1), (1, -1, 0)]
    else:
        raise RuntimeError("Unknown root system")
    roots = sorted(roots); indices = {v: i for i, v in enumerate(roots)}
    coeffs = [coordinates(kind, v) for v in roots]
    for v, c in zip(roots, coeffs):
        require(v == tuple(sum(c[j]*simple[j][i] for j in range(len(simple)))
                           for i in range(len(v))), "Wrong simple-root coordinate conversion")
        require(all(x >= 0 for x in c) or all(x <= 0 for x in c), "Root has mixed simple signs")
    generators = []
    for alpha in simple:
        norm = sum(x*x for x in alpha); reflection = []
        for v in roots:
            numerator = 2*sum(x*y for x, y in zip(v, alpha))
            require(numerator % norm == 0, "Nonintegral reflection coefficient")
            image = tuple(x - numerator//norm*y for x, y in zip(v, alpha))
            require(image in indices, "Explicit roots are not closed under reflection")
            reflection.append(indices[image])
        require(len(set(reflection)) == len(roots), "A reflection is not a permutation")
        generators.append(tuple(reflection))
    return roots, coeffs, [indices[a] for a in simple], generators


def build_group(kind):
    roots, coeffs, simple_ids, generators = root_system(kind)
    identity = tuple(range(len(roots))); elements = [identity]; lookup = {identity: 0}
    words = [()]; edges = []
    for element in elements:
        word = words[lookup[element]]; next_elements = []
        for letter, generator in enumerate(generators, 1):
            following = tuple(element[i] for i in generator)
            if following not in lookup:
                lookup[following] = len(elements); elements.append(following)
                words.append(word + (letter,))
            next_elements.append(lookup[following])
        edges.append(tuple(next_elements))
    expected_order = {"A3": 24, "B3": 48, "C3": 48, "C2": 8, "F4": 1152, "G2": 12}[kind]
    require(len(elements) == expected_order, f"{kind}: wrong Weyl group order")
    positive = [i for i, c in enumerate(coeffs) if all(x >= 0 for x in c)]
    for element, word in zip(elements, words):
        inverted = sum(all(x <= 0 for x in coeffs[element[i]]) for i in positive)
        require(inverted == len(word), "BFS length disagrees with positive-root inversion count")
    return {"elements": elements, "words": words, "edges": edges,
            "coeffs": coeffs, "simple_ids": simple_ids}


def evaluate(group, word, omitted=()):
    state = 0; omitted = set(omitted)
    for j, letter in enumerate(word):
        if j not in omitted:
            state = group["edges"][state][letter - 1]
    return state


def centres(group):
    answer = {}
    for w, word in enumerate(group["words"]):
        for omitted in range(len(word)):
            state = 0
            for j, letter in enumerate(word):
                if j == omitted:
                    continue
                following = group["edges"][state][letter - 1]
                if len(group["words"][following]) > len(group["words"][state]):
                    state = following
            answer.setdefault((w, state), []).append(omitted + 1)
    return answer


def character_data(group, word, omitted_positions, columns):
    omitted = {j - 1 for j in omitted_positions}; rank = len(group["simple_ids"])
    require(len(omitted) == len(omitted_positions) and all(0 <= j < len(word) for j in omitted),
            "Illegal mask witness")
    state = 0; chars = {}
    for j, letter in enumerate(word):
        if j in omitted:
            if j + 1 in columns:
                root = group["elements"][state][group["simple_ids"][letter - 1]]
                chars[j + 1] = tuple(-x for x in group["coeffs"][root])
        else:
            if j + 1 in columns:
                chars[j + 1] = (0,) * rank
            state = group["edges"][state][letter - 1]
    return state, [chars[j] for j in columns]


def determinant(matrix):
    n = len(matrix); require(all(len(row) == n for row in matrix), "Nonsquare minor")
    return sum((-1)**sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
               * prod(matrix[i][p[i]] for i in range(n)) for p in permutations(range(n)))


def verify(kind, certificate_dir):
    data = json.loads((certificate_dir / f"{kind}_certificate.json").read_text())
    group = build_group(kind); exact = centres(group)
    histogram = Counter(len(group["words"][w])-len(group["words"][u]) for w, u in exact)
    require(dict(histogram) == {int(k): v for k, v in data["all_exact_centre_gap_histogram"].items()},
            "Complete deletion-centre coverage differs")
    require(len(exact) == data["all_exact_centre_count"], "Wrong total centre count")
    row_count = 0; case_count = 0; minor_count = 0
    for test in data["tests"]:
        gap = test["summary"]["dimension"]; records = test["records"]
        expected = {pair for pair in exact if len(group["words"][pair[0]])-len(group["words"][pair[1]]) == gap}
        observed = set()
        for record in records:
            word = tuple(record["word_w"]); w = evaluate(group, word)
            u = evaluate(group, record["word_u"]); pair = (w, u)
            require(pair not in observed, "Duplicate certificate case"); observed.add(pair)
            require(word == group["words"][w] and tuple(record["word_u"]) == group["words"][u],
                    "Stored word differs from independently chosen reduced word")
            columns = record["exact_columns"]
            require(columns == exact[pair], "Incomplete exceptional column set")
            endpoint, reference = character_data(group, word, record["reference_omitted_positions"], columns)
            require(endpoint == u, "Reference mask has wrong endpoint")
            rows = record["raw_rows"]
            require(len(rows) == len(record["row_witnesses"]), "Missing row witness")
            for row, witness in zip(rows, record["row_witnesses"]):
                endpoint, chars = character_data(group, word, witness["omitted_positions"], columns)
                a = witness["root_coordinate"] - 1
                require(endpoint == u and 0 <= a < len(group["simple_ids"]), "Invalid endpoint or coordinate")
                require(row == [c[a]-r[a] for c, r in zip(chars, reference)], "Raw character row differs")
            total = 0
            for minor in record["bezout_minors"]:
                indices = [i - 1 for i in minor["row_indices"]]
                require(len(indices) == len(columns) and len(set(indices)) == len(indices)
                        and all(0 <= i < len(rows) for i in indices), "Invalid full-column minor")
                value = determinant([rows[i] for i in indices])
                require(value == minor["determinant"], "Leibniz determinant differs")
                total += minor["bezout_coefficient"] * value
            require(total == record["maximal_minor_gcd"] and total > 0, "Bezout identity failed")
            if total != 1:
                require(len(columns) == 1, "Unexpected multicolumn nonprimitive case")
                all_gcd = 0
                for bits in product((0, 1), repeat=len(word)):
                    omitted = [j + 1 for j, bit in enumerate(bits) if not bit]
                    endpoint, chars = character_data(group, word, omitted, columns)
                    if endpoint == u:
                        for a in range(len(group["simple_ids"])):
                            all_gcd = gcd(all_gcd, abs(chars[0][a]-reference[0][a]))
                require(all_gcd == total, "Complete exceptional-mask gcd differs")
            case_count += 1; row_count += len(rows); minor_count += len(record["bezout_minors"])
        require(observed == expected, f"{kind}: omitted or extraneous cases at gap {gap}")
    print(f"PASS independent root permutations {kind}: {len(group['words'])} group elements, "
          f"{case_count} cases, {row_count} rows, {minor_count} minors.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate-dir", type=Path, default=Path(__file__).resolve().parent / "generated")
    args = parser.parse_args()
    for kind in ("A3", "B3", "C3", "C2", "F4", "G2"):
        verify(kind, args.certificate_dir)
    print("ALL INDEPENDENT ROOT-PERMUTATION CHECKS PASSED.")


if __name__ == "__main__":
    main()
