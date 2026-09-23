# Changelog (reverse chronological):
# 2026-08-02 - Claude: created. Derives the conjectured n=7,d=3 Hilbert
#   series from Snellman-Moreno-Socias's Conjecture 6.2 (arXiv:math/0007089
#   -- see ../literature/REFERENCES.md and ../LOGBOOK.md's 2026-08-02
#   entry) and re-expresses it "in base binomial" (Jan's term; = this
#   project's "binomial basis", see binomial_basis.py) using
#   a=kozlov_vector(7). Companion to
#   snellman-morenosocias_n7d3_verify.m2, which checks the same
#   conjectured series against an actual Macaulay2 computation.

from fractions import Fraction as F


def binomial(n, k):
    if k < 0 or k > n:
        return 0
    num = 1
    for i in range(k):
        num = num * (n - i)
    den = 1
    for i in range(1, k + 1):
        den = den * i
    return num // den


def kozlov_vector(n):
    return [binomial(n, i) for i in range(1, n + 1)]


def conjectured_q_n3(n):
    """
    Conjecture 6.2's formula, read as giving q_{n,3}(t) (the Hilbert series
    of the QUOTIENT bigwedge V_n/(f) for f a generic cubic form) -- NOT
    p_{n,3}(t) (the ideal's series) despite the paper's own labeling; see
    ../LOGBOOK.md's 2026-08-02 entry for why. Returns the list of
    coefficients [q_0, q_1, ..., q_n].

    L_n(t) depends on n mod 4 (Conjecture 6.2); only the n=4l+3 case is
    implemented here (needed for n=7), since c_1(n), c_2(n) in the n=4l+1
    case are only described as "some positive integers", not pinned down
    by the paper.
    """
    d = 3
    if n % 4 != 3:
        raise NotImplementedError(
            "only the n=4l+3 case of L_n(t) is implemented (paper leaves "
            "n=4l+1's c_1(n),c_2(n) unspecified; n=4l,4l+2 not needed here)"
        )
    ell = (n - 3) // 4

    def poly_mul(a, b):
        res = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                res[i + j] += ai * bj
        return res

    def poly_pow(a, k):
        res = [1]
        for _ in range(k):
            res = poly_mul(res, a)
        return res

    # L_n(t) = (3t)^(2l+1) * (1+t), for n = 4l+3
    threet_pow = poly_pow([0, 3], 2 * ell + 1)   # (3t)^(2l+1)
    one_plus_t = [1, 1]
    L_n = poly_mul(threet_pow, one_plus_t)

    # numerator = t^d * L_n(t) + (1+t)^n
    shifted = [0] * d + L_n
    ambient = poly_pow([1, 1], n)
    maxlen = max(len(shifted), len(ambient))
    shifted += [0] * (maxlen - len(shifted))
    ambient += [0] * (maxlen - len(ambient))
    numerator = [shifted[i] + ambient[i] for i in range(maxlen)]

    # divide by (1 + t^d), expected exact (remainder 0)
    divisor = [1] + [0] * (d - 1) + [1]
    quotient = [0] * (len(numerator) - len(divisor) + 1)
    rem = numerator[:]
    for i in range(len(quotient) - 1, -1, -1):
        coeff = rem[i + len(divisor) - 1]
        quotient[i] = coeff
        for j, dv in enumerate(divisor):
            rem[i + j] -= coeff * dv
    assert all(r == 0 for r in rem), f"division not exact, remainder={rem}"

    q = quotient + [0] * (n + 1 - len(quotient))
    return q[: n + 1]


def to_base_binomial(values, a):
    """
    "base binomial" (Jan's term) / binomial-basis coordinates of a vector
    (values[1],...,values[n]) w.r.t. a=(a_1,...,a_n): the barycentric
    coordinates w.r.t. the vertices of angle(a) -- see
    right-angle-simplices-notes.md's "Binomial basis of R^n" section.
    y_j = values[j]/a[j] - values[j+1]/a[j+1]  (j<n),  y_n = values[n]/a[n].
    `values` and `a` are both 1-indexed lists of length n+1 (index 0 unused)
    for readability.
    """
    n = len(a) - 1
    y = [None] * (n + 1)
    for j in range(1, n + 1):
        cur = F(values[j], a[j])
        nxt = F(values[j + 1], a[j + 1]) if j < n else F(0)
        y[j] = cur - nxt
    return y[1:]


if __name__ == "__main__":
    n = 7
    q = conjectured_q_n3(n)
    print(f"conjectured q_{{{n},3}}(t) coefficients (degree 0..{n}):", q)

    a = kozlov_vector(n)
    print(f"a = kozlov_vector({n}) =", a)

    # drop q_0 (trivial degree-0 term), match the f_1..f_n convention
    q_tail = [None] + q[1:]  # 1-indexed, q_tail[1..n] = q[1..n]
    a_1idx = [None] + a
    y = to_base_binomial(q_tail, a_1idx)
    print("base-binomial coordinates y_1..y_7:", [str(v) for v in y])
    print("sum(y) =", sum(y), " (expect q_1/a_1 =", F(q[1], a[0]), ")")
