#!/usr/bin/env python3
"""Independent exact tensor-graph verifier (Python 3.10+, standard library).

No imports from verify_counterexample.py, no Apery vectors, and no matrix ranks.
The conductor blocks and lower value bounds are checked from DP membership.
The paper proves connectivity beyond a0+b0+4*c, so the finite range is exhaustive.
All tests use explicit exceptions (not assert), so python -O retains the checks.
"""
from __future__ import annotations

from collections import deque
import json


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def membership_table(generators: tuple[int, ...], limit: int) -> list[bool]:
    require(bool(generators) and min(generators) > 0, 'Positive generators required.')
    require(limit >= 0, 'Negative table bound.')
    table = [False] * (limit + 1)
    table[0] = True
    # Forward reachability differs from the shortest-path and backward-DP checks.
    for n in range(limit + 1):
        if table[n]:
            for g in generators:
                if n + g <= limit:
                    table[n + g] = True
    return table


def components(vertices: list[int], gamma: list[bool]) -> list[list[int]]:
    """Vertices are first coordinates; the second coordinate is d-u.

    The exact edge condition is |u-v| in Gamma. Removing newly reached
    vertices avoids materializing the dense edge set.
    """
    unseen = set(vertices)
    result: list[list[int]] = []
    while unseen:
        first = min(unseen)
        unseen.remove(first)
        queue = deque([first])
        component = [first]
        while queue:
            current = queue.popleft()
            neighbors = sorted(u for u in unseen if gamma[abs(u - current)])
            unseen.difference_update(neighbors)
            queue.extend(neighbors)
            component.extend(neighbors)
        result.append(sorted(component))
    return result


def check_case(generators: tuple[int, ...], a: int, b: int, conductor: int,
               expected_torsion: bool) -> dict[str, object]:
    require(0 < a <= b, 'The ideal generators must have 0 < a <= b.')
    require(conductor > 0, 'A positive conductor is expected in these examples.')
    # V = {v : v+a,v+b in Gamma}; necessarily v >= -a, and c-a is in V.
    # b0 <= c-a, so the tail bound never exceeds 5*c in these cases.
    limit = 5 * conductor + a + b + 10
    table = membership_table(generators, limit)

    def member(n: int) -> bool:
        if n < 0:
            return False
        require(n <= limit, 'Membership lookup exceeds the proved table bound.')
        return table[n]

    m = min(generators)
    require(not member(conductor - 1), 'The proposed Frobenius number is not a gap.')
    require(all(member(n) for n in range(conductor, conductor + m)),
            'The complete conductor block is absent.')
    # Adding m propagates this complete block to every larger integer.
    require(member(a) and member(b), 'The ideal is not integral.')
    b0 = next(v for v in range(-a, conductor - a + 1)
              if member(v + a) and member(v + b))
    a0 = a
    threshold = a0 + b0 + 4 * conductor
    require(threshold < limit, 'Internal bound calculation failed.')
    nonempty = 0
    disconnected: list[dict[str, object]] = []
    max_vertices = 0
    total_vertices = 0
    torsion_dimension = 0
    for degree in range(a0 + b0, threshold):
        vertices = [u for u in range(a0, degree - b0 + 1)
                    if (member(u - a) or member(u - b))
                    and member(degree - u + a) and member(degree - u + b)]
        if not vertices:
            continue
        nonempty += 1
        max_vertices = max(max_vertices, len(vertices))
        total_vertices += len(vertices)
        parts = components(vertices, table)
        if len(parts) > 1:
            torsion_dimension += len(parts) - 1
            disconnected.append({'degree': degree, 'component_count': len(parts),
                                 'first_coordinate_components': parts})
    require(bool(disconnected) == expected_torsion,
            f'Unexpected tensor torsion for generators {generators}, ideal {(a,b)}.')
    return {
        'generators': list(generators), 'ideal_exponents': [a,b],
        'conductor': conductor, 'a0':a0, 'b0':b0,
        'checked_degree_start': a0 + b0,
        'checked_degree_end_inclusive': threshold - 1,
        'automatic_connectivity_from': threshold,
        'nonempty_graphs_checked':nonempty,
        'total_vertices_checked':total_vertices,
        'largest_graph_vertices':max_vertices,
        'disconnected_graphs':len(disconnected),
        'total_torsion_dimension':torsion_dimension,
        'first_torsion_witness':disconnected[0] if disconnected else None
    }


def main() -> None:
    main_result = check_case(
        (56,57,58,63,64,70,71,72,73,74,75,76,77,78,79,80,81,82,83,
         87,89,90,93,95,96,97), 56, 70, 182, False)
    require(main_result['a0'] == 56 and main_result['b0'] == 0,
            'Main-example lower value bounds are wrong.')
    require(main_result['automatic_connectivity_from'] == 784,
            'The claimed exhaustive tail bound is wrong.')
    controls = [
        check_case((2,3), 2,3,2,True),
        check_case((4,5,6),4,5,8,True),
        check_case((4,5,6),4,8,8,False),  # (t^4,t^8) = t^4 R.
    ]
    print(json.dumps({'status':'PASS',
        'method':'Independent dynamic programming and exact graph connectivity.',
        'main_example':main_result,'controls':controls,
        'field_independent':True,
        'scope':'Finite graph checks plus the paper\'s proved uniform tail bound.'},
        indent=2))


if __name__ == '__main__':
    main()
