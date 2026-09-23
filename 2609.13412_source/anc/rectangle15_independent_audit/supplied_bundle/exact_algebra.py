"""Exact character and witness coefficients. Python standard library only.

No supplied cone matrix is used: central rows are reconstructed from character
sums by marked-cycle enumeration, and branching rows from content differences.
Partitions are weakly decreasing tuples of positive integers.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial, gcd, lcm, prod

Partition = tuple[int, ...]

@lru_cache(None)
def partitions(n: int, cap: int | None = None) -> tuple[Partition, ...]:
    if n < 0:
        raise ValueError('negative partition size')
    if n == 0:
        return ((),)
    cap = min(n, n if cap is None else cap)
    return tuple((j,) + a for j in range(cap, 0, -1)
                 for a in partitions(n-j, j))

@lru_cache(None)
def dimension(a: Partition) -> int:
    return factorial(sum(a)) // prod(
        a[i]-j+sum(v > j for v in a[i+1:])
        for i in range(len(a)) for j in range(a[i]))

@lru_cache(None)
def content_sum(a: Partition) -> int:
    return sum(v*(v-1)//2-i*v for i, v in enumerate(a))

@lru_cache(None)
def z(rho: Partition) -> int:
    return prod(k**m*factorial(m) for k, m in Counter(rho).items())

@lru_cache(None)
def character(a: Partition, rho: Partition) -> int:
    """Murnaghan--Nakayama in beta-set form; exact integer output."""
    if not rho:
        return int(not a)
    r, ell = rho[0], len(a)
    beads = [v+ell-i-1 for i, v in enumerate(a)]
    answer = 0
    for b in beads:
        t = b-r
        if t < 0 or t in beads:
            continue
        sign = (-1)**sum(t < c < b for c in beads)
        moved = sorted([c for c in beads if c != b]+[t], reverse=True)
        smaller = tuple(v-ell+i+1 for i, v in enumerate(moved)
                        if v-ell+i+1 > 0)
        answer += sign*character(smaller, rho[1:])
    return answer


def primitive(v: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    g = gcd(*v)
    if not g:
        raise ArithmeticError('zero generator requested')
    return tuple(t//g for t in v)


def removable(a: Partition) -> tuple[tuple[Partition, int], ...]:
    return tuple((a[:i]+((a[i]-1,) if a[i]>1 else ())+a[i+1:], a[i]-i-1)
                 for i in range(len(a))
                 if i == len(a)-1 or a[i] > a[i+1])


def addable(a: Partition) -> tuple[tuple[Partition, int], ...]:
    return tuple((a[:i]+(a[i]+1,)+a[i+1:], a[i]-i)
                 for i in range(len(a)) if i == 0 or a[i-1] > a[i]) \
           + ((a+(1,), -len(a)),)


def branching_row(beta: Partition, gamma: Partition,
                  parts: tuple[Partition, ...]) -> tuple[int, ...]:
    c = dict(removable(beta)).get(gamma)
    if c is None:
        raise ValueError('gamma is not a one-box predecessor of beta')
    if any(sum(nu) != sum(beta)+1 for nu in parts):
        raise ValueError('partition order mismatch')
    entries = {}
    for nu, d in addable(beta):
        if c == d:
            raise ArithmeticError('zero axial distance')
        entries[nu] = Fraction(1, d-c)
    L = lcm(*(v.denominator for v in entries.values()))
    return primitive([int(L*entries.get(nu, 0)) for nu in parts])


@lru_cache(None)
def cycles(p: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    seen = set()
    result = []
    for i in range(len(p)):
        if i in seen:
            continue
        block = []
        j = i
        while j not in seen:
            seen.add(j)
            block.append(j)
            j = p[j]
        result.append(tuple(block))
    return tuple(result)


def canonical(rho: Partition) -> tuple[int, ...]:
    out = []
    j = 0
    for r in rho:
        out.extend(list(range(j+1, j+r))+[j])
        j += r
    return tuple(out)


@lru_cache(None)
def compositions(n: int, k: int) -> tuple[tuple[int, ...], ...]:
    if k == 0:
        return ((),) if n == 0 else ()
    if k == 1:
        return ((n,),)
    return tuple((j,)+tail for j in range(n+1)
                 for tail in compositions(n-j, k-1))


@lru_cache(None)
def marked_states(p: int, k: int):
    return tuple((a, rho, factorial(p-k)//z(rho))
                 for m in range(p-k+1)
                 for a in compositions(m, k)
                 for rho in partitions(p-k-m))


def type_with_tails(cc, a, tail):
    return tuple(sorted(tail+tuple(len(c)+sum(a[i] for i in c)
                                   for c in cc), reverse=True))


def marked_cycle_counts(p: int, q: int, k: int) -> dict:
    """Counts (type(sigma),type(pi),type((sigma+pi)tau_k)).

    All k! permutations on the second set of marks are enumerated. For the
    first set, simultaneous relabelling permits conjugacy-class reduction.
    """
    if not 1 <= k <= min(p, q):
        raise ValueError('invalid swap count')
    A, B = marked_states(p, k), marked_states(q, k)
    ts = [(tuple(t), cycles(tuple(t))) for t in permutations(range(k))]
    raw = defaultdict(int)
    for sr in partitions(k):
        s = canonical(sr)
        sc = cycles(s)
        multiplicity = factorial(k)//z(sr)
        ainfo = [(a, r, w*multiplicity, type_with_tails(sc, a, r))
                 for a, r, w in A]
        for t, tc in ts:
            cc = cycles(tuple(s[t[i]] for i in range(k)))
            tc_images = tuple(tuple(t[i] for i in block) for block in cc)
            binfo = [(b, r, w, type_with_tails(tc, b, r),
                      tuple(sum(b[i] for i in block) for block in cc))
                     for b, r, w in B]
            for a, r, w, rtype in ainfo:
                aa = tuple(2*len(block)+sum(a[j] for j in image)
                           for block, image in zip(cc, tc_images))
                for b, rr, ww, stype, bb in binfo:
                    ntype = tuple(sorted(r+rr+tuple(v+u for v, u in zip(aa, bb)),
                                         reverse=True))
                    raw[(rtype, stype, ntype)] += w*ww
    if sum(raw.values()) != factorial(p)*factorial(q):
        raise ArithmeticError('marked-cycle total is incorrect')
    marginals = defaultdict(int)
    for (r, s, t), v in raw.items():
        marginals[r, s] += v
    for r in partitions(p):
        for s in partitions(q):
            if marginals[r, s] != factorial(p)//z(r)*(factorial(q)//z(s)):
                raise ArithmeticError('marked-cycle marginal is incorrect')
    return dict(raw)


def central_row(alpha: Partition, beta: Partition, k: int,
                parts: tuple[Partition, ...], counts: dict | None = None
                ) -> tuple[int, ...]:
    p, q = sum(alpha), sum(beta)
    if any(sum(nu) != p+q for nu in parts):
        raise ValueError('partition order mismatch')
    if k == 1:
        # Restriction multiplicity times total-content difference.  This is a
        # positive scalar multiple of the same character sum used for k>=2.
        vals = []
        for nu in parts:
            numerator = sum(
                (factorial(p)//z(r))*(factorial(q)//z(s))
                * character(alpha, r)*character(beta, s)
                * character(nu, tuple(sorted(r+s, reverse=True)))
                for r in partitions(p) for s in partitions(q))
            den = factorial(p)*factorial(q)
            if numerator % den:
                raise ArithmeticError('nonintegral restriction multiplicity')
            multiplicity = numerator//den
            if multiplicity < 0:
                raise ArithmeticError('negative restriction multiplicity')
            vals.append(multiplicity*(content_sum(nu)-content_sum(alpha)
                                     -content_sum(beta)))
        return primitive(vals)
    if counts is None:
        counts = marked_cycle_counts(p, q, k)
    h = defaultdict(int)
    for (r, s, t), v in counts.items():
        h[t] += v*character(alpha, r)*character(beta, s)
    return primitive([sum(v*character(nu, t) for t, v in h.items())
                      for nu in parts])
