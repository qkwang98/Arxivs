"""Verify the illustrated finite minimal-resolution strands using only stdlib.

Run from any working directory. All matrices are reconstructed from polynomial
boundaries in illustrated-strands-data.json. Integer elimination uses only unit
pivots; a zero residual proves the stated rank and unit Smith factors over Z.
No saved rank or geometric assertion is accepted as a substitute for a check.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement
from math import prod
from pathlib import Path
import json

DATA = json.loads(Path(__file__).with_name("illustrated-strands-data.json").read_text())
LIMIT = DATA["prime_support_through"]
assert LIMIT >= 39  # Every total label in the requested strands is at most 42-3.
A = tuple(n for n in range(3, LIMIT + 1, 2)
          if all(n % p for p in range(2, int(n**0.5) + 1)))
GENERATORS = DATA["generators"]
BY_ID = {g["id"]: g for g in GENERATORS}
assert len(BY_ID) == len(GENERATORS)
assert BY_ID["1"] == {"id": "1", "h": 0, "n": 0, "d": 0, "boundary": []}

@lru_cache(None)
def monomials(n, d):
    if d < 0 or n < 3*d:
        return ()
    if d == 0:
        return ((),) if n == 0 else ()
    return tuple(t for t in combinations_with_replacement(
        tuple(a for a in A if a <= n), d) if sum(t) == n)

def terms(g):
    result = defaultdict(int)
    for term in g["boundary"]:
        mon = tuple(sorted(term["monomial"]))
        result[(term["target"], mon)] += int(term["coefficient"])
    return {key: value for key, value in result.items() if value}

for g in GENERATORS[1:]:
    assert g["boundary"], g["id"]
    for (target, mon), coefficient in terms(g).items():
        t = BY_ID[target]
        assert mon and all(p in A for p in mon), (g["id"], target, mon)
        assert t["h"] == g["h"] - 1
        assert t["n"] + sum(mon) == g["n"]
        assert t["d"] + len(mon) == g["d"]
        assert isinstance(coefficient, int)

# Completeness and exact orientation of all chosen quadratic stars.
expected_quadratics = set()
for n in range(6, 43):
    pairs = monomials(n, 2)
    if pairs:
        anchor = max(pairs, key=prod)
        for leaf in pairs:
            if leaf != anchor:
                expected_quadratics.add((n, leaf, anchor))
actual_quadratics = set()
for g in GENERATORS:
    if g["h"] != 1:
        continue
    assert g["d"] == 2 and 6 <= g["n"] <= 42
    b = terms(g)
    assert len(b) == 2 and sorted(b.values()) == [-1, 1]
    anchor = next(mon for (target, mon), c in b.items() if c == 1)
    leaf = next(mon for (target, mon), c in b.items() if c == -1)
    assert all(target == "1" for target, mon in b)
    actual_quadratics.add((g["n"], leaf, anchor))
assert actual_quadratics == expected_quadratics
assert len(actual_quadratics) == sum(g["h"] == 1 for g in GENERATORS)

# Internal certificate identifiers are stable; printed labels use increasing
# positive product gap in each quadratic fiber. The anchor has coefficient +1.
expected_labels = {}
for n in sorted({g["n"] for g in GENERATORS if g["h"] == 1}):
    fiber = []
    for g in GENERATORS:
        if g["h"] == 1 and g["n"] == n:
            gap = sum(c*prod(mon) for (target, mon), c in terms(g).items())
            assert gap > 0
            fiber.append((gap, g["id"]))
    for prime_count, (gap, gid) in enumerate(sorted(fiber)):
        expected_labels[gid] = {"name": f"e{n},2" + "'"*prime_count,
                                "product_gap": gap}
assert DATA["quadratic_display_labels"] == expected_labels
assert expected_labels["e1_22_2_1"] == {"name": "e22,2'", "product_gap": 64}
assert expected_labels["e1_24_2_2"] == {"name": "e24,2", "product_gap": 24}
assert expected_labels["e1_24_2_1"] == {"name": "e24,2'", "product_gap": 48}
assert expected_labels["e1_42_2_3"] == {"name": "e42,2", "product_gap": 60}
assert expected_labels["e1_42_2_2"] == {"name": "e42,2'", "product_gap": 96}
assert expected_labels["e1_42_2_1"] == {"name": "e42,2''", "product_gap": 252}

@lru_cache(None)
def basis(h, n, d):
    return tuple((g["id"], mon) for g in GENERATORS
                 if g["h"] == h and g["d"] <= d
                 for mon in monomials(n-g["n"], d-g["d"]))

def differential(h, n, d):
    rows, columns = basis(h-1, n, d), basis(h, n, d)
    row_index = {row: i for i, row in enumerate(rows)}
    matrix = [[0]*len(columns) for _ in rows]
    for j, (gid, mon) in enumerate(columns):
        for (target, coefficient_mon), coefficient in terms(BY_ID[gid]).items():
            row = (target, tuple(sorted(mon + coefficient_mon)))
            assert row in row_index
            matrix[row_index[row]][j] += coefficient
    return matrix, rows, columns

def unit_rank(matrix, column_count):
    """Unimodular row/column reduction; fail if a nonzero residual survives."""
    m = [row[:] for row in matrix]
    rows, columns = len(m), column_count
    assert all(len(row) == columns for row in m)
    k = 0
    while k < min(rows, columns):
        pivot = next(((i, j) for i in range(k, rows)
                      for j in range(k, columns) if abs(m[i][j]) == 1), None)
        if pivot is None:
            break
        i, j = pivot
        m[k], m[i] = m[i], m[k]
        for row in m:
            row[k], row[j] = row[j], row[k]
        unit = m[k][k]
        for i in range(k+1, rows):
            multiplier = m[i][k] // unit
            if multiplier:
                m[i] = [x-multiplier*y for x, y in zip(m[i], m[k])]
        # Clear the rest of the pivot row by integral column operations.
        for j in range(k+1, columns):
            multiplier = m[k][j] // unit
            if multiplier:
                for i in range(rows):
                    m[i][j] -= multiplier*m[i][k]
        k += 1
    assert not any(m[i][j] for i in range(k, rows)
                   for j in range(k, columns)), "Nonzero residual after unit pivots"
    return k

def check_composition(left, right, right_columns):
    middle = len(right)
    assert all(len(row) == middle for row in left)
    assert all(len(row) == right_columns for row in right)
    assert all(sum(left[i][k]*right[k][j] for k in range(middle)) == 0
               for i in range(len(left)) for j in range(right_columns))

def component_count(matrix, vertex_count):
    parent = list(range(vertex_count))
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    column_count = len(matrix[0]) if matrix else 0
    for j in range(column_count):
        ends = [(i, matrix[i][j]) for i in range(vertex_count) if matrix[i][j]]
        assert len(ends) == 2 and sorted(c for i, c in ends) == [-1, 1]
        u, v = (i for i, c in ends)
        parent[find(u)] = find(v)
    return len({find(v) for v in range(vertex_count)})

def check_strand(n, d):
    dimensions = [len(basis(h, n, d)) for h in range(d)]
    assert all(p <= n-3*(d-1) for mon in monomials(n, d) for p in mon)
    matrices = []
    ranks = []
    for h in range(1, d):
        matrix, rows, columns = differential(h, n, d)
        assert len(rows) == dimensions[h-1] and len(columns) == dimensions[h]
        ranks.append(unit_rank(matrix, len(columns)))
        if matrices:
            check_composition(matrices[-1], matrix, len(columns))
        matrices.append(matrix)
    homology = [dimensions[h] - ([0]+ranks)[h] - (ranks+[0])[h]
                for h in range(d)]
    assert not any(homology[1:]), (n, d, homology)
    assert homology[0] == component_count(matrices[0], dimensions[0])
    return dict(bidegree=[n, d], dimensions=dimensions, ranks=ranks,
                homology=homology, all_nonzero_smith_factors_are_units=True)

# Check the generator degrees, not merely their later appearances in (34,4).
cubic_checks = [check_strand(n, 3) for n in range(9, 32)
                if monomials(n, 3)]
for item in cubic_checks:
    assert item["ranks"][-1] == item["dimensions"][-1]
assert all(g["d"] == 3 and g["n"] <= 31
           for g in GENERATORS if g["h"] == 2)
assert [(g["n"], g["d"]) for g in GENERATORS if g["h"] == 3] == [(34, 4)]

requested = []
for nd, dimensions, ranks in zip(DATA["requested_strands"],
                                 DATA["expected_dimensions"],
                                 DATA["expected_ranks"]):
    item = check_strand(*nd)
    assert item["dimensions"] == dimensions and item["ranks"] == ranks
    requested.append(item)

# The printed F31 boundaries differ from the certificate basis by signs only.
assert terms(BY_ID["e2_31_3_1"]) == {
    ("e1_18_2_1", (13,)): 1, ("e1_24_2_1", (7,)): -1,
    ("e1_26_2_2", (5,)): 1}
assert terms(BY_ID["e2_31_3_2"]) == {
    ("e1_14_2_1", (17,)): 1, ("e1_20_2_1", (11,)): -1,
    ("e1_24_2_2", (7,)): 1}
assert terms(BY_ID["e2_31_3_3"]) == {
    ("e1_18_2_1", (13,)): 1, ("e1_20_2_1", (11,)): -1,
    ("e1_26_2_1", (5,)): 1, ("e1_28_2_1", (3,)): -1}
assert DATA["illustrated_cubic_basis_at_31"] == {
    "e2_31_3_1": {"name": "e31,3'", "sign": 1},
    "e2_31_3_2": {"name": "e31,3''", "sign": 1},
    "e2_31_3_3": {"name": "e31,3", "sign": -1}}

top = BY_ID[DATA["pyramid_top_generator"]]
assert terms(top) == {
    ("e2_21_3_1", (13,)): 1, ("e2_23_3_1", (11,)): -1,
    ("e2_27_3_1", (7,)): -1, ("e2_29_3_2", (5,)): 1,
    ("e2_31_3_1", (3,)): -1}
assert terms(BY_ID["e2_21_3_1"]) == {
    ("e1_10_2_1", (11,)): 1, ("e1_16_2_1", (5,)): -1,
    ("e1_18_2_1", (3,)): 1}

vertices = {name: tuple(mon) for name, mon in DATA["pyramid_vertices"].items()}
assert vertices == {"U": (3, 7, 11, 13), "A": (3, 5, 13, 13),
                    "B": (5, 5, 11, 13), "C": (5, 7, 11, 11),
                    "D": (3, 5, 7, 19)}
vertex_name = {mon: name for name, mon in vertices.items()}
edges = {}
face_sets = []
for (face, multiplier), face_sign in terms(top).items():
    adjacency = defaultdict(set)
    face_vertices = set()
    for (quadratic, mon), incidence in terms(BY_ID[face]).items():
        mon = tuple(sorted(mon + multiplier))
        key = (quadratic, mon)
        ends = {}
        for (target, pair), sign in terms(BY_ID[quadratic]).items():
            assert target == "1" and sign in (-1, 1)
            ends[sign] = vertex_name[tuple(sorted(mon + pair))]
        assert len(ends) == 2
        origin, end = ends[-1], ends[1]
        assert prod(vertices[origin]) < prod(vertices[end])
        adjacency[origin].add(end)
        adjacency[end].add(origin)
        face_vertices.update((origin, end))
        if key not in edges:
            edges[key] = dict(origin=origin, end=end, incidences=[])
        assert (edges[key]["origin"], edges[key]["end"]) == (origin, end)
        edges[key]["incidences"].append(face_sign*incidence)
    assert all(len(neighbors) == 2 for neighbors in adjacency.values())
    reached = set()
    stack = [next(iter(face_vertices))]
    while stack:
        v = stack.pop()
        if v not in reached:
            reached.add(v)
            stack.extend(adjacency[v] - reached)
    assert reached == face_vertices
    face_sets.append(frozenset(face_vertices))
assert len(edges) == 8
assert all(sorted(edge["incidences"]) == [-1, 1] for edge in edges.values())
assert set(face_sets) == {frozenset(face) for face in
                        [["U", "A", "B"], ["U", "B", "C"], ["U", "C", "D"],
                         ["U", "D", "A"], ["A", "B", "C", "D"]]}
assert len(face_sets) == 5

print(json.dumps({
    "status": "PASS",
    "quadratic_star_generators_checked": len(actual_quadratics),
    "quadratic_anchor_sign_and_increasing_gap_labels_checked": True,
    "cubic_generator_strands_checked": len(cubic_checks),
    "strands": requested,
    "pyramid_boundary_f_vector": [5, 8, 5],
    "pyramid_face_cycles_and_opposite_edge_incidences_checked": True,
    "scope": "The pyramid is the support of the unique 3-cell, not the whole strand."
}, indent=2))

