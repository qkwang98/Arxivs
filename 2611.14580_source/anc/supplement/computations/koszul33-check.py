"""Integral check of the four polygon-to-Koszul classes in bidegree (33,3).

A key (r,i,j), with i<j, denotes x_r epsilon_i epsilon_j.  Coordinates in
K_1 are indexed by the exterior label: every quadratic fiber at a fixed
weight is one free abelian group in the binary Goldbach quotient.
Run with Python 3.9+; the check has no external dependencies or inputs.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import isqrt


def wedge(r, i, j):
    if i == j:
        return Counter()
    key = (r, min(i, j), max(i, j))
    assert sum(key) == 33
    return Counter({key: 1 if i < j else -1})


def combine(*terms):
    result = Counter()
    for coefficient, chain in terms:
        for key, value in chain.items():
            result[key] += coefficient * value
    return Counter({key: value for key, value in result.items() if value})


def chain(*terms):
    return combine(*((sign, wedge(r, i, j)) for sign, r, i, j in terms))


def boundary2(vector):
    result = Counter()
    for (r, i, j), value in vector.items():
        result[j] += value
        result[i] -= value
    return {p: value for p, value in result.items() if value}


def boundary3(a, b, c):
    return chain((1, a, b, c), (-1, b, a, c), (1, c, a, b))


def determinant(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    size = len(rows)
    assert all(len(row) == size for row in rows)
    result = Fraction(1)
    for j in range(size):
        pivot = next((i for i in range(j, size) if rows[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            rows[pivot], rows[j] = rows[j], rows[pivot]
            result = -result
        result *= rows[j][j]
        for i in range(j+1, size):
            factor = rows[i][j] / rows[j][j]
            for k in range(j+1, size):
                rows[i][k] -= factor * rows[j][k]
    return result


primes = [p for p in range(3, 34, 2)
          if all(p % t for t in range(2, isqrt(p)+1))]
triples = [u for u in combinations_with_replacement(primes, 3) if sum(u) == 33]
named = dict(zip("ABCDEFGH", triples))
assert len(named) == 8 and named["H"] == (11, 11, 11)
labels = sorted({p for u in triples for p in u})
graph_edges = {}
for p in labels:
    leaves = [u for u in triples if p in u]
    # Removing the same factor from each endpoint leaves the quadratic fiber.
    def pair_score(u):
        a, b, c = u
        return a*b*c // p
    anchor = max(leaves, key=pair_score)
    for u in leaves:
        if u != anchor:
            edge = frozenset((anchor, u))
            assert edge not in graph_edges
            graph_edges[edge] = p
assert len(graph_edges) == 11

def face_chain(face):
    vertices = [named[letter] for letter in face]
    fixed = [graph_edges[frozenset((u, v))]
             for u, v in zip(vertices, vertices[1:] + vertices[:1])]
    turns = []
    for j, u in enumerate(vertices):
        incoming, outgoing = fixed[j-1], fixed[j]
        if incoming != outgoing:
            turns.append((1, wedge(sum(u)-incoming-outgoing, incoming, outgoing)))
    return combine(*turns)


triangle, left, right, upper = map(face_chain, ("ACG", "BCGF", "ACED", "BCEH"))
assert triangle == chain((1,23,7,3), (1,17,3,13), (1,13,13,7))
assert left == chain((1,11,19,3), (1,17,3,13), (1,13,13,7), (1,7,7,19))
assert right == chain((1,7,23,3), (1,13,3,17), (1,11,17,5), (1,5,5,23))
assert upper == chain((1,19,11,3), (1,13,3,17), (1,5,17,11))

triangle_swaps = chain((1,13,13,7), (1,3,7,23), (-1,7,3,23),
                       (1,13,3,17), (-1,3,13,17))
left_swaps = chain((1,7,7,19), (1,13,13,7), (1,13,3,17), (-1,3,11,19),
                   (-1,3,13,17), (-1,19,3,11))
assert triangle_swaps == combine((1, triangle), (1, boundary3(*named["A"])),
                                 (-1, boundary3(*named["C"])))
assert left_swaps == combine((1, left), (-1, boundary3(*named["B"])),
                             (-1, boundary3(*named["C"])))
user_left_support = ((7,7,19), (13,13,7), (13,3,17), (3,11,19))
for signs in product((-1,1), repeat=4):
    assert boundary2(chain(*((s,*term) for s,term in zip(signs,user_left_support))))

edges = set()
for u in triples:
    for i,j in combinations(sorted(set(u)), 2):
        edges.add((33-i-j,i,j))
boundaries = [boundary3(*u) for u in triples if len(set(u)) == 3]
faces = [triangle, left, right, upper]
assert (len(labels), len(edges), len(boundaries)) == (8,15,4)
assert all(not boundary2(z) and z.keys() <= edges for z in faces + boundaries)

# The integral cycle lattice of the K_2 -> K_1 incidence graph is freely
# parametrized by its coefficients on edges outside a spanning forest.
parent = {p: p for p in labels}
def root(p):
    while parent[p] != p:
        p = parent[p]
    return p
chords = []
for edge in sorted(edges):
    _,i,j = edge
    if root(i) != root(j):
        parent[root(i)] = root(j)
    else:
        chords.append(edge)
matrix = [[z[edge] for z in boundaries + faces] for edge in chords]
index = determinant(matrix)
assert len(chords) == 8 and abs(index) == 1

repeated = [(13,7,13), (7,7,19), (5,5,23)]
marker_matrix = [[z[e] for z in faces] for e in repeated]
assert abs(determinant([row[:3] for row in marker_matrix])) == 1
assert all(row[-1] == 0 for row in marker_matrix)
print("PASS: (33,3) Koszul ranks K1=8 K2=15 K3=4; four signed polygon cycles.")
print("Three K2 square coordinates (rows), triangle/left/right/upper (columns):",
      marker_matrix)
print("Integral determinant of four K3 boundaries and four face cycles in chord coordinates:", index)
print("Verified both signed swap formulas and the three-term upper cycle.")
