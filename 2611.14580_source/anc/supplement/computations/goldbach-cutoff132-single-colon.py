"""The cutoff-132 single-colon obstruction. Requires Python 3."""
from collections import defaultdict, deque
from itertools import combinations_with_replacement
from math import isqrt


def odd_primes(cutoff):
    return [p for p in range(3, cutoff, 2)
            if all(p % j for j in range(3, isqrt(p) + 1, 2))]


def pair_fibers(cutoff):
    groups = defaultdict(list)
    for p, q in combinations_with_replacement(odd_primes(cutoff), 2):
        groups[p + q].append((p, q))
    return groups


def explore(start, target, groups):
    """Breadth-first search through all binary moves until target or exhaustion."""
    start, target = tuple(sorted(start)), tuple(sorted(target))
    predecessor = {start: None}
    queue = deque([start])
    while queue:
        x = queue.popleft()
        if x == target:
            path = []
            while x is not None:
                path.append(x)
                x = predecessor[x]
            return path[::-1], len(predecessor)
        for i, p in enumerate(x):
            if i and x[i - 1] == p:
                continue
            for j in range(i + 1, len(x)):
                if j > i + 1 and x[j] == x[j - 1]:
                    continue
                fixed = x[:i] + x[i + 1:j] + x[j + 1:]
                for pair in groups[p + x[j]]:
                    neighbor = tuple(sorted(fixed + pair))
                    if neighbor not in predecessor:
                        predecessor[neighbor] = x
                        queue.append(neighbor)
    return [], len(predecessor)


def main():
    groups = pair_fibers(132)
    lhs, rhs = (127,) * 6, (107,) + (131,) * 5
    assert sum(lhs) == sum(rhs) == 762 and len(lhs) == len(rhs) == 6
    assert groups[254] == [(127, 127)]
    left, right = (3,) + lhs, (3,) + rhs
    path, left_count = explore(left, right, groups)
    assert not path and left_count == 211
    path, right_count = explore(right, left, groups)
    assert not path and right_count == 322
    print("Disconnected single-multiplier components:", left_count, right_count)
    path, _ = explore((3,) + left, (3,) + right, groups)
    assert len(path) == 8
    print("Shortest path with multiplier x3^2:")
    for vertex in path:
        print(*vertex)

    # Admitting 137 supplies the previously absent three-and-three profile.
    larger_groups = pair_fibers(138)
    bridge = (3, 113, 127, 127, 127, 131, 137)
    assert sum(bridge) == sum(left)
    assert sum(p % 3 == 1 for p in bridge) == 3
    assert sum(p % 3 == 2 for p in bridge) == 3
    path, _ = explore(left, right, larger_groups)
    assert len(path) == 9
    to_bridge, _ = explore(left, bridge, larger_groups)
    from_bridge, _ = explore(bridge, right, larger_groups)
    assert to_bridge and from_bridge
    print("Cutoff 138: shortest singly multiplied path has eight moves.")
    print("Reachable three-and-three profile:", *bridge)


if __name__ == "__main__":
    main()

