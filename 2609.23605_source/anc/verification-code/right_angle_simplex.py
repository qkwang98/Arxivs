# Changelog (reverse chronological):
# 2026-07-31 - Claude: added right_angle_ones_hrepresentation(n, d), a
#   closed-form H-representation (one equation, a "capped staircase" chain
#   of inequalities) of R = \angle(1,...,1) + shift^d(\angle(1,...,1)) for
#   the intermediate case 1 <= d <= n-1, built directly from the formula
#   rather than from right_angle_minkowski_sum's vertices. Verified equal
#   (as Sage Polyhedron objects, P == C) to right_angle_minkowski_sum's
#   output for every n=2..10, d=1..n-1 (45 cases) -- see the function's
#   docstring and ../artefacts/right-angle-simplices-notes.md's new section
#   for the derivation and worked n=5,d=1 example. Answers item 1 of
#   ../artefacts/research-roadmap.md for a=all-ones.
# 2026-07-30 - Claude: refined chain_order_complex_simplex(n)'s docstring
#   against Stanley 1986 ("Two Poset Polytopes", ../literature/): computed
#   its actual H-representation and found it's affinely isomorphic to
#   O(chain_{n-1}) (Stanley's order polytope, one element short of the naive
#   n-chain guess), not literally O(chain_n).
# 2026-07-30 - Claude: confirmed kozlov_simplex(n) against Kozlov 1997
#   ("Convex Hulls of f- and beta-Vectors", ../literature/), Theorem 4.1: its
#   F~_i(n) = (binom(n,1),...,binom(n,i),0,...,0) is literally our v_i, so
#   kozlov_simplex(n) = conv{F~_1,...,F~_n} exactly, matching the theorem
#   verbatim (not just analogous to it). Updated docstring accordingly.
# 2026-07-30 - Claude: added right_angle_simplex_vertices (factored out of
#   right_angle_simplex, so the v_1,...,v_n order is available directly
#   rather than relying on Polyhedron.vertices_list(), which may reorder)
#   and extremal_matrix(a, d), for the r=2, d_1=0 case: M[i][j] = 1 iff
#   v_i + shift^d(v_j) is a vertex of \angle(a) + shift^d(\angle(a)).
#   Corrected/renamed version of essential_mat in
#   ../artefacts/rightangular.org (which took two arbitrary vertex lists;
#   this version is specialized to the A, shift^d(A) case at hand and fixes
#   the vertex order explicitly).
# 2026-07-30 - Claude: added the two named special cases of \angle(a): all-ones
#   a (ones_vector/chain_order_complex_simplex, per Gemini's claim that this is
#   the order complex of a chain) and the binomial-coefficients a
#   (kozlov_vector/kozlov_simplex, claimed by definition to be the Kozlov
#   simplex). Both claims are from ../transcripts/, not independently verified
#   here -- flagged as such in the docstrings.
# 2026-07-30 - Claude: added pad_vector/pad_polytope/right_angle_minkowski_sum.
#   Sage's Polyhedron '+' (Minkowski sum) requires matching ambient
#   dimension, so each shift^{d_i}(\angle(a)) must be padded with trailing
#   zeros up to R^N, N = len(a) + max(degs), before summing -- same
#   embedding trick as ufill() in ../artefacts/rightangular.org, but now
#   composed from shift_polytope rather than duplicated inline.
# 2026-07-30 - Claude: added shift_vector/shift_polytope, implementing the
#   shift operator (shift(a_0,a_1,...) = (0,a_0,a_1,...), applied entrywise
#   to a polytope's vertices) so that shift^d(right_angle_simplex(a)) can be
#   formed as a step towards Minkowski sums of shifted copies. Adopted
#   \angle(a) as short notation for right_angle_simplex(a).
# 2026-07-30 - Claude: created this file. Corrected version of trunkL/
#   rangle_simplex from ../artefacts/rightangular.org: that code's trunkL
#   ran its truncation index k over range(n+1), so its k=0 term was
#   L[:0] + [0]*n = (0,...,0) -- an erroneous extra vertex at the origin.
#   right_angle_simplex here starts the truncation at 1, giving exactly the
#   n intended vertices, no more.

"""
The right-angle simplex spanned by a vector of positive integers, and the
shift operator on R^infty (eventually-zero real sequences).

Setup: for a = (a_1, ..., a_n), a vector of positive integers, the
right-angle simplex, denoted \angle(a), is the simplex in R^n spanned by

    v_1 = (a_1, 0, ..., 0)
    v_2 = (a_1, a_2, 0, ..., 0)
    ...
    v_n = (a_1, a_2, ..., a_n)

i.e. v_i = (a_1, ..., a_i, 0, ..., 0). Note v_i - v_{i-1} = a_i * e_i, so
consecutive vertices differ along a single coordinate axis -- hence
"right-angle".

shift: R^infty -> R^infty is shift(a_0, a_1, a_2, ...) = (0, a_0, a_1, ...),
prepending a zero. For a in R^n and d >= 0, shift^d(a) is naturally viewed
in R^(n+d). shift_polytope applies this entrywise to a polytope's vertices,
so shift_polytope(\angle(a), d) is shift^d(\angle(a)) in R^(n+d).

right_angle_minkowski_sum(a, degs), for degs = (d_1, ..., d_r) a weakly
increasing sequence of non-negative integers, forms

    shift^{d_1}(\angle(a)) + shift^{d_2}(\angle(a)) + ... + shift^{d_r}(\angle(a))

(Minkowski sum), embedded in R^N with N = len(a) + max(degs).

Two special choices of a are of particular interest (see
../artefacts/right-angle-simplices-notes.md for the running discussion):

- a = (1, ..., 1) (n ones): \angle(a) is claimed (Gemini, see ../transcripts/)
  to be the order complex of a chain on n elements.
- a = (binom(n,1), ..., binom(n,n)): \angle(a) is the Kozlov simplex,
  confirmed against Kozlov 1997, Theorem 4.1 (see kozlov_simplex below).
"""


def right_angle_simplex_vertices(a):
    """
    a: list of n positive integers
    returns [v_1, ..., v_n], the vertices of \angle(a) in this specific
    order (v_i = (a_1, ..., a_i, 0, ..., 0)) -- kept separate from
    right_angle_simplex so callers that need to know which vertex is which
    (e.g. extremal_matrix) don't have to rely on Polyhedron.vertices_list(),
    whose order is not guaranteed to match.
    """
    n = len(a)
    return [a[:i] + [0] * (n - i) for i in range(1, n + 1)]


def right_angle_simplex(a):
    """
    a: list of n positive integers
    returns the Polyhedron \angle(a) in R^n spanned by
    v_i = (a_1, ..., a_i, 0, ..., 0), i = 1, ..., n
    """
    return Polyhedron(vertices=right_angle_simplex_vertices(a))


def shift_vector(v, d):
    """
    v: list of numbers, a point in R^n
    d: non-negative integer
    returns shift^d(v) = d zeros prepended to v, a point in R^(n+d)
    """
    return [0] * d + list(v)


def shift_polytope(P, d):
    """
    P: Polyhedron in R^n
    d: non-negative integer
    returns shift^d(P), the Polyhedron in R^(n+d) obtained by applying
    shift^d to every vertex of P
    """
    vertices = [shift_vector(v, d) for v in P.vertices_list()]
    return Polyhedron(vertices=vertices)


def pad_vector(v, N):
    """
    v: list of numbers, a point in R^m, m <= N
    returns v with trailing zeros appended to reach length N, i.e. the
    same point viewed in R^N under the standard inclusion R^m -> R^N
    """
    return list(v) + [0] * (N - len(v))


def pad_polytope(P, N):
    """
    P: Polyhedron in R^m, m <= N
    returns P embedded in R^N by padding every vertex with trailing zeros
    """
    vertices = [pad_vector(v, N) for v in P.vertices_list()]
    return Polyhedron(vertices=vertices)


def right_angle_minkowski_sum(a, degs):
    """
    a: list of n positive integers
    degs: list of r non-negative integers d_1, ..., d_r (weakly increasing
    by convention; order does not affect the result since Minkowski sum is
    commutative)
    returns the Minkowski sum of shift^{d_i}(right_angle_simplex(a)) for
    i = 1, ..., r, embedded in R^N, N = len(a) + max(degs)
    """
    N = len(a) + max(degs)
    P = right_angle_simplex(a)
    summands = [pad_polytope(shift_polytope(P, d), N) for d in degs]
    Q = summands[0]
    for S in summands[1:]:
        Q = Q + S
    return Q


def extremal_matrix(a, d):
    """
    a: list of n positive integers
    d: non-negative integer

    Let A = \angle(a), with vertices v_1, ..., v_n (right_angle_simplex_vertices
    order), B = shift^d(A), with vertices u_j = shift^d(v_j), and
    C = A + B (Minkowski sum, the r=2, d_1=0, d_2=d case of
    right_angle_minkowski_sum).

    Returns the n x n 0/1 matrix M (indices 0-based, so M[i][j] corresponds
    to v_{i+1} + u_{j+1}) with M[i][j] = 1 iff v_i + u_j is extremal, i.e. a
    vertex of C, else 0.

    d=0 gives B=A and C=2A (dilation), whose vertices are exactly {2 v_i};
    v_i + u_j = v_i + v_j is extremal only for i=j, so M is the identity
    matrix. Large d (relative to n) makes A and B's coordinate ranges
    disjoint, giving C the Cartesian (prism) product structure with all n^2
    sums extremal, i.e. M all-ones.
    """
    n = len(a)
    N = n + d
    V = right_angle_simplex_vertices(a)
    Vp = [tuple(pad_vector(v, N)) for v in V]
    U = [tuple(shift_vector(v, d)) for v in V]
    C = right_angle_minkowski_sum(a, [0, d])
    C_vertices = set(tuple(v) for v in C.vertices_list())
    return matrix(ZZ, n, n, lambda i, j: 1 if tuple(
        x + y for x, y in zip(Vp[i], U[j])) in C_vertices else 0)


def ones_vector(n):
    """
    n: positive integer
    returns (1, 1, ..., 1), n ones
    """
    return [1] * n


def chain_order_complex_simplex(n):
    """
    n: positive integer
    returns \angle(ones_vector(n)) = \angle(1, ..., 1).

    Claim (Gemini, see ../transcripts/): this is (combinatorially) the order
    complex of a chain on n elements, i.e. an (n-1)-simplex -- confirmed, but
    also fairly immediate (any n-element chain's order complex is trivially
    an (n-1)-simplex).

    Refined (2026-07-30) against Stanley 1986's *order polytope* O(P)
    (../literature/): this is NOT literally O(chain_n) (that has n+1
    vertices, including an all-zero one -- exactly what the old buggy
    trunkL/rangle_simplex in ../artefacts/rightangular.org would give). It
    is affinely isomorphic to O(chain_{n-1}) -- one element short -- via
    dropping the redundant coordinate x_1, which is pinned to 1 by an
    equation here (the substantive discrepancy) rather than merely bounded
    x_1<=1 as in a genuine n-dimensional order polytope. (Its inequality
    chain also runs in the order-reversed direction from Stanley's
    convention, but that's just the antitone-vs-isotone convention split in
    the literature, not an error.) See
    ../artefacts/right-angle-simplices-notes.md for the computed
    H-representation and full discussion.
    """
    return right_angle_simplex(ones_vector(n))


def kozlov_vector(n):
    """
    n: positive integer
    returns (binom(n,1), binom(n,2), ..., binom(n,n))
    """
    return [binomial(n, k) for k in range(1, n + 1)]


def kozlov_simplex(n):
    """
    n: positive integer
    returns \angle(kozlov_vector(n)) = \angle(binom(n,1), ..., binom(n,n)).

    Confirmed (2026-07-30) against Kozlov 1997, "Convex Hulls of f- and
    beta-Vectors" (../literature/), Theorem 4.1: that theorem's F~_i(n) =
    (binom(n,1),...,binom(n,i),0,...,0) is exactly our v_i, so this *is*
    conv{F~_1,...,F~_n}, the simplex of Theorem 4.1 -- the convex hull of
    f-vectors of all simplicial complexes on n vertices -- verbatim, not
    just analogously.
    """
    return right_angle_simplex(kozlov_vector(n))


def right_angle_ones_hrepresentation(n, d):
    """
    Closed-form H-representation of R = \\angle(a) + shift^d(\\angle(a)) for
    a = ones_vector(n) = (1,...,1), in the intermediate case 1 <= d <= n-1
    (d=0 is the trivial dilation R=2A; d>=n-1 is the Cartesian/prism product,
    Corollary cor:cartesian in ../artefacts/extremal-matrix-ones.tex).

    Built directly from the formula below -- no reference to
    right_angle_minkowski_sum or vertex enumeration -- as R's ambient R^N
    (N=n+d, coords x_1,...,x_N, 1-indexed; A occupies coords 1..n, B =
    shift^d(A) occupies coords d+1..N, m=n-d of them shared):

        x_1 = 1                                                (equation)
        1 = x_1 >= x_2 >= ... >= x_d                            (A-only block)
        x_{d+1} <= x_d + 1,  x_{d+1} >= 1                       (entry into overlap)
        x_{d+1} >= x_{d+2} >= ... >= x_n                        (overlap block)
        x_n >= x_{n+1}                                          (transition, no bump)
        x_{n+1} <= 1                                            (B-only ceiling)
        x_{n+1} >= x_{n+2} >= ... >= x_N                        (B-only block)
        x_N >= 0                                                (floor)

    i.e. a single weakly-decreasing chain x_2 >= ... >= x_N, floored at 0 and
    capped at 1 at both ends, except the first overlap coordinate x_{d+1} may
    go one unit higher (up to x_d+1 <= 2) -- the "+1 bump" is exactly the
    coordinate where a vertex of A and a vertex of B can simultaneously
    contribute a 1. Any of the four internal chains is empty when its two
    endpoints coincide (d=1 empties the A-only and B-only chains; m=1 empties
    the overlap chain, and then the "transition" inequality becomes
    redundant, implied by x_{d+1}>=1 and x_{n+1}<=1 through the single shared
    coordinate -- matching the known d=n-1 Cartesian-product facet count 2n).

    Returns (eqns, ieqs) in Sage Polyhedron convention: each row is
    [b, a_1, ..., a_N] meaning b + a.x = 0 (eqns) or b + a.x >= 0 (ieqs).
    Construct the polytope itself via Polyhedron(eqns=eqns, ieqs=ieqs).

    Verified (2026-07-31): Polyhedron(eqns=eqns, ieqs=ieqs) ==
    right_angle_minkowski_sum(ones_vector(n), [0, d]) for every n=2..10,
    d=1..n-1 (45 cases, exact Polyhedron equality, not just matching
    vertex/facet counts). See ../artefacts/right-angle-simplices-notes.md's
    "H-representation of R for a=all-ones" section for the derivation, and
    ../artefacts/research-roadmap.md item 1, which this answers for
    a=all-ones (the a=Kozlov-vector analogue, item 2, is still open).
    """
    assert 1 <= d <= n - 1
    N = n + d

    def e(k):
        v = [0] * N
        v[k - 1] = 1
        return v

    def step(k):
        return [a - b for a, b in zip(e(k), e(k + 1))]

    eqns = [[-1] + e(1)]
    ieqs = []
    for k in range(1, d):
        ieqs.append([0] + step(k))
    ieqs.append([1] + step(d))
    ieqs.append([-1] + e(d + 1))
    for k in range(d + 1, n):
        ieqs.append([0] + step(k))
    ieqs.append([0] + step(n))
    ieqs.append([1] + [-c for c in e(n + 1)])
    for k in range(n + 1, N):
        ieqs.append([0] + step(k))
    ieqs.append([0] + e(N))
    return eqns, ieqs
