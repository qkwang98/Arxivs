"""Exact, standard-library-only coefficients for symmetric-block witnesses.

Mathematical justification is in proof.md.  Partitions are decreasing tuples.
No floating-point operations are used here.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
from math import comb, factorial, gcd, prod
from typing import Iterable

Partition = tuple[int, ...]

@lru_cache(None)
def partitions(n: int, cap: int | None = None) -> tuple[Partition, ...]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return ((),)
    cap = min(n, n if cap is None else cap)
    return tuple((j,) + tail for j in range(cap, 0, -1)
                 for tail in partitions(n-j, j))

@lru_cache(None)
def dimension(lam: Partition) -> int:
    hooks = (lam[i]-j+sum(t > j for t in lam[i+1:])
             for i in range(len(lam)) for j in range(lam[i]))
    return factorial(sum(lam)) // prod(hooks)

def horizontal(nu: Partition, beta: Partition) -> bool:
    length = max(len(nu), len(beta)) + 1
    v = nu + (0,) * (length-len(nu))
    b = beta + (0,) * (length-len(beta))
    return all(v[i] >= b[i] >= v[i+1] for i in range(length-1))

def horizontal_children(beta: Partition, p: int) -> tuple[Partition, ...]:
    """Pieri children, without enumerating all partitions of p+|beta|."""
    tail = beta[1:] + (0,)
    ranges = [range(lo, hi+1) for lo, hi in zip(tail, beta)]
    answer = []
    for lower in product(*ranges):
        first = sum(beta)+p-sum(lower)
        nu = tuple(x for x in (first,)+lower if x)
        if first >= beta[0] and horizontal(nu, beta):
            answer.append(nu)
    return tuple(sorted(set(answer), reverse=True))

def newton_coefficient(nu: Partition, beta: Partition, p: int, k: int) -> int:
    if sum(nu) != sum(beta)+p or not 0 <= k <= p:
        raise ValueError("inconsistent order or contraction length")
    if not horizontal(nu, beta):
        return 0
    b = beta + (0,)*len(nu)
    contents = tuple(j-i for i, row in enumerate(nu)
                     for j in range(b[i], row))
    if len(contents) != p:
        raise ArithmeticError("wrong strip size")
    r = p-k
    value = sum((-1)**(r-j)*comb(r, j)
                * prod(j-p+1+c for c in contents) for j in range(r+1))
    if value % factorial(r):
        raise ArithmeticError("Newton coefficient was not integral")
    return value // factorial(r)

def witness(p: int, beta: Partition, k: int) -> dict[Partition, int]:
    if not 1 <= k <= min(p, sum(beta)):
        raise ValueError("contraction length must be between 1 and min(p,q)")
    return {nu: x for nu in horizontal_children(beta, p)
            if (x := newton_coefficient(nu, beta, p, k))}

def primitive_witness(p: int, beta: Partition, k: int) -> dict[Partition, int]:
    row = witness(p, beta, k)
    g = 0
    for x in row.values():
        g = gcd(g, abs(x))
    return {nu: x//g for nu, x in row.items()} if g else {}

def family_shapes(m: int) -> tuple[Partition, ...]:
    return ((m+4,3,3), (m+3,4,3), (m+3,3,3,1),
            (m+2,4,3,1), (m+2,3,3,2), (m+1,4,3,2),
            (m+1,3,3,3), (m,4,3,3))

def family_columns(m: int) -> tuple[tuple[int, int, int], ...]:
    """Columns D=Phi(4,m33,3), E=Phi(m,433,1), F=Phi(m+1,333,2)."""
    return (
        (4*m*(m-2)*(m-1), 4*m, 3*m*(m+1)),
        ((m-3)*(m-2)*(m-1), 3*m-1, 0),
        ((m-18)*(m-2)*(m-1), 3*(m-2), m*(m-9)),
        (-6*(m-3)*(m-2), 2*(m-3), 0),
        (-10*(m-7)*(m-2), 2*(m-5), -4*(2*m-5)),
        (30*(m-3), m-9, 0),
        (60*(m-4), m-12, 36),
        (-120, -10, 0),
    )

def family_coefficients(m: int) -> tuple[int, ...]:
    return (3*m*(17*m*m+74*m-351),
            9*(m-3)*(m*m+27*m-8),
            14*m**3+21*m*m-711*m+1296,
            18*(m-3)*(7*m-24),
            10*(5*m*m-41*m+114),
            90*(m-3)*(m-6),
            90*(m-1)*(m-6),
            -180*(5*m-9))
