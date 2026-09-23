# Changelog (reverse chronological):
# 2026-08-02 - Claude: added verify_against_jts_forskning_note(), cross-checking
#   shift_matrix_binomial_formula_a against an independent, earlier derivation
#   of the same question found in jts-forskning/projekt/exteriorconvex/
#   exteriorconvex.tex (migrated here as ../artefacts/exterior-convex.tex) --
#   see ../artefacts/binomial-basis-shift-crosscheck.typ for the writeup.
# 2026-08-02 - Claude: added worked_example_n4_d2_ones(), the concrete
#   n=4, d=2, a=(1,1,1,1) case shown by hand in chat, plus an all-ones/
#   generic-a case list passed to verify_shift_formula_general_a in
#   __main__ (previously only exercised via ad-hoc session calls, not
#   committed here).
# 2026-08-02 - Claude: generalized from the Kozlov-specific a=kozlov_vector(n)
#   to arbitrary positive-integer a: S_matrix_a/T_matrix_a/
#   shift_matrix_binomial_formula_a take a directly (the old n-only functions
#   are now thin wrappers calling these with a=kozlov_vector(n)). Added
#   enumerate_lattice_points_a/lattice_image_condition_a, characterizing
#   (proved, not just checked -- see right-angle-simplices-notes.md) exactly
#   which points of the standard simplex are T(a)-images of integer lattice
#   points inside right_angle_simplex(a), for general a. Answers Jan's
#   follow-up "for general a" question from the same session.
# 2026-08-02 - Claude: created this file. Implements the "binomial basis"
#   {v_1,...,v_n} of R^n (v_i = kozlov_simplex vertices), the change-of-basis
#   matrices S(n) [columns = v_i, standard->binomial] / T(n) = S(n)^-1, the
#   matrix of shift^d in the binomial basis (both by direct conjugation and a
#   derived closed form -- see ../artefacts/right-angle-simplices-notes.md's
#   "Binomial basis" section for the derivation), and a Kruskal-Katona
#   shadow-bound implementation used to enumerate/characterize which lattice
#   points inside the Kozlov simplex are actually f-vectors of simplicial
#   complexes on n vertices. Answers Jan's four-part question from the
#   2026-08-02 session (see LOGBOOK.md).

"""
The "binomial basis" of R^n: v_1,...,v_n, the vertices of the Kozlov simplex
\\angle(kozlov_vector(n)) (see right_angle_simplex.py), used as a basis of R^n
(not just as a spanning set of an (n-1)-dim simplex).

Convention (fixed 2026-08-02 with Jan): S(n) = [v_1 | v_2 | ... | v_n], the
matrix with the v_i as COLUMNS (in standard coordinates). This is the
"standard" change-of-basis matrix: for x in standard coordinates,
x = S(n) [x]_v, i.e. [x]_v = T(n) x with T(n) := S(n)^-1.

For a linear map F: R^n -> R^n with matrix A w.r.t. the standard basis, its
matrix B w.r.t. the binomial basis is the ordinary similarity transform
    B = T(n) A S(n) = S(n)^-1 A S(n).

Kruskal-Katona: f-vectors here are indexed by cardinality, f_i = number of
faces of size i (i = 1,...,n; this excludes the empty face), matching Kozlov
1997 Theorem 4.1's F~_k(n) = (binom(n,1),...,binom(n,k),0,...,0) convention
already confirmed in right_angle_simplex.py. In this convention, (f_1,...,f_n)
is the f-vector of some simplicial complex on (a subset of) n labeled
vertices iff f_1 <= n and, for i=2,...,n, f_i <= shadow_bound(f_{i-1}, i)
(the Kruskal-Katona upper bound, kk_shadow_bound below) -- both necessary
(classical) and sufficient (achieved by an appropriate compressed/colex
complex at each level; verified computationally below by brute force for
n=4).
"""

from itertools import combinations


def kk_cascade(m, i):
    """
    The i-cascade (i-th binomial) representation of m >= 0: unique list of
    pairs [(a_i, i), (a_{i-1}, i-1), ..., (a_j, j)] with
    a_i > a_{i-1} > ... > a_j >= j >= 1 and
    m = binomial(a_i, i) + binomial(a_{i-1}, i-1) + ... + binomial(a_j, j).
    Returns [] if m == 0. Requires i >= 1.
    """
    terms = []
    remaining = m
    level = i
    a_bound = None  # next chosen a must be strictly less than this
    while remaining > 0 and level >= 1:
        a = level - 1  # binomial(level-1, level) = 0, valid starting point
        while binomial(a + 1, level) <= remaining and (a_bound is None or a + 1 < a_bound):
            a += 1
        terms.append((a, level))
        remaining -= binomial(a, level)
        a_bound = a
        level -= 1
    assert remaining == 0, (m, i, terms, remaining)
    return terms


def kk_shadow_bound(m, i):
    """
    Kruskal-Katona upper bound on f_i given f_{i-1} = m (cardinality
    convention, i >= 2). Returns max achievable f_i.
    """
    if m == 0:
        return 0
    return sum(binomial(a, level + 1) for (a, level) in kk_cascade(m, i - 1))


def enumerate_f_vectors(n):
    """
    All (f_1,...,f_n) achievable as f-vectors (cardinality convention) of a
    simplicial complex on (a subset of) n labeled vertices, via the
    Kruskal-Katona recursion: f_1 in 0..n, f_i in 0..kk_shadow_bound(f_{i-1}, i).
    Returns a list of tuples.
    """
    results = []

    def rec(prefix):
        i = len(prefix) + 1
        if i > n:
            results.append(tuple(prefix))
            return
        if i == 1:
            hi = n
        else:
            hi = kk_shadow_bound(prefix[-1], i)
        for f_i in range(hi + 1):
            rec(prefix + [f_i])

    rec([])
    return results


def brute_force_f_vectors(n):
    """
    Ground-truth check (small n only): enumerate ALL simplicial complexes on
    n labeled vertices (all downward-closed subsets of the 2^n - 1 nonempty
    subsets of {1,...,n}) by brute force, and return the SET of f-vectors
    (cardinality convention) actually achieved. Only feasible for n <= 4
    (2^(2^n - 1) candidate families).
    """
    verts = range(1, n + 1)
    nonempty = []
    for k in range(1, n + 1):
        nonempty.extend(combinations(verts, k))
    nonempty_set = set(nonempty)
    m = len(nonempty)
    achieved = set()
    for mask in range(2 ** m):
        chosen = [nonempty[j] for j in range(m) if (mask >> j) & 1]
        chosen_set = set(chosen)
        # downward closure check
        ok = True
        for face in chosen:
            if len(face) > 1:
                for sub in combinations(face, len(face) - 1):
                    if sub not in chosen_set:
                        ok = False
                        break
                if not ok:
                    break
        if not ok:
            continue
        f = [0] * n
        for face in chosen:
            f[len(face) - 1] += 1
        achieved.add(tuple(f))
    return achieved


def S_matrix_a(a):
    """
    S(a) = [v_1 | ... | v_n], columns = vertices of right_angle_simplex(a),
    for ANY list of n positive integers a (n = len(a)). Generalizes S_matrix
    (which is just S_matrix_a(kozlov_vector(n))).
    """
    load('right_angle_simplex.py')  # noqa: brings in right_angle_simplex_vertices
    vs = right_angle_simplex_vertices(list(a))
    return matrix(QQ, vs).transpose()


def T_matrix_a(a):
    """T(a) = S(a)^-1: converts standard coordinates to a's binomial-basis coordinates."""
    return S_matrix_a(a).inverse()


def S_matrix(n):
    """S(n) = S_matrix_a(kozlov_vector(n)): the Kozlov-specific case."""
    load('right_angle_simplex.py')  # noqa: brings in kozlov_vector
    return S_matrix_a(kozlov_vector(n))


def T_matrix(n):
    """T(n) = S(n)^-1: converts standard coordinates to binomial-basis coordinates."""
    return S_matrix(n).inverse()


def binomial_coords_from_fvector(f):
    """
    Direct formula (bypasses matrix multiplication) for T(n)*f, using T's
    bidiagonal structure: y_j = f_j/a_j - f_{j+1}/a_{j+1} for j<n, y_n = f_n/a_n.
    a_i = binomial(n,i), n = len(f). Equivalent to T_matrix(n)*vector(f).
    """
    n = len(f)
    a = [binomial(n, i) for i in range(1, n + 1)]
    y = [QQ(f[j]) / a[j] - QQ(f[j + 1]) / a[j + 1] for j in range(n - 1)]
    y.append(QQ(f[n - 1]) / a[n - 1])
    return y


def is_density_monotone(f):
    """
    Check f_1/a_1 >= f_2/a_2 >= ... >= f_n/a_n (a_i=binomial(n,i)) --
    equivalent to all binomial_coords_from_fvector(f) entries being >= 0.
    Proved (2026-08-02, elementary double-counting, see
    right-angle-simplices-notes.md) to hold for every f-vector of an
    (n-vertex) simplicial complex.
    """
    return all(c >= 0 for c in binomial_coords_from_fvector(f))


def shift_matrix_standard(n, d):
    """N^d: matrix of shift^d: R^n -> R^n (shift(x_1,...,x_n)=(0,x_1,...,x_{n-1})) in the standard basis."""
    N = matrix(QQ, n, n)
    for i in range(1, n):
        N[i, i - 1] = 1
    return N ** d


def shift_matrix_binomial_direct(n, d):
    """Matrix of shift^d in the binomial basis, by direct conjugation T*N^d*S."""
    S = S_matrix(n)
    T = S.inverse()
    return T * shift_matrix_standard(n, d) * S


def shift_matrix_binomial_formula_a(a, d):
    """
    Matrix of shift^d in the binomial basis for GENERAL positive-integer a
    (n = len(a)), via the closed form derived 2026-08-02 (see
    right-angle-simplices-notes.md -- the derivation never used a_i =
    binomial(n,i) specifically, only that a is a positive vector, so this
    generalizes verbatim). With c_i := a_i / a_{i+d} for i=0,...,n-d+1
    (c_0 := 0, c_{n-d+1} := 0), B_d is zero in rows 1..d-1, and for
    j = d,...,n (i := j-d):
      - if i == 0: row j is constant, equal to c_0 - c_1 = -c_1
      - if i >= 1: (B_d)_{j,k} = 0 for k < i, = c_i for k = i,
                    = c_i - c_{i+1} for k > i
    """
    n = len(a)
    aa = [None] + list(a)  # 1-indexed: aa[1],...,aa[n]
    B = matrix(QQ, n, n)
    if d >= n:
        return B  # zero matrix

    def c(i):
        if i == 0 or i == n - d + 1:
            return QQ(0)
        return QQ(aa[i]) / QQ(aa[i + d])

    for j in range(d, n + 1):  # 1-indexed row
        i = j - d
        for k in range(1, n + 1):  # 1-indexed column
            if i == 0:
                B[j - 1, k - 1] = -c(1)
            elif k < i:
                B[j - 1, k - 1] = 0
            elif k == i:
                B[j - 1, k - 1] = c(i)
            else:
                B[j - 1, k - 1] = c(i) - c(i + 1)
    return B


def shift_matrix_binomial_formula(n, d):
    """Kozlov-specific case: shift_matrix_binomial_formula_a(kozlov_vector(n), d)."""
    load('right_angle_simplex.py')  # noqa
    return shift_matrix_binomial_formula_a(kozlov_vector(n), d)


def verify_shift_formula(n_max=8):
    """Check shift_matrix_binomial_formula against direct conjugation for n=2..n_max, d=0..n."""
    for n in range(2, n_max + 1):
        for d in range(0, n + 1):
            direct = shift_matrix_binomial_direct(n, d)
            formula = shift_matrix_binomial_formula(n, d)
            if direct != formula:
                return False, (n, d)
    return True, None


def verify_shift_formula_general_a(cases):
    """
    Check shift_matrix_binomial_formula_a against direct conjugation
    T(a)*N^d*S(a) for a list of (a, d) test cases (a arbitrary positive
    integer lists, not just kozlov_vector).
    """
    for a, d in cases:
        n = len(a)
        S = S_matrix_a(a)
        T = S.inverse()
        direct = T * shift_matrix_standard(n, d) * S
        formula = shift_matrix_binomial_formula_a(a, d)
        if direct != formula:
            return False, (a, d)
    return True, None


def enumerate_lattice_points_a(a):
    """
    All integer points x in Z^n (n=len(a)) lying in right_angle_simplex(a):
    x_1 = a_1 (forced -- the simplex lies in this hyperplane), and, for
    j=2,...,n, x_j in 0..floor(a_j * x_{j-1} / a_{j-1}) (the H-representation
    "x_j/a_j <= x_{j-1}/a_{j-1}, ratios non-increasing" derived from writing
    x as a convex combination of the v_i and reading off the tail sums --
    see right-angle-simplices-notes.md). Returns a list of tuples.
    """
    a = list(a)
    n = len(a)
    results = []

    def rec(prefix):
        j = len(prefix) + 1
        if j > n:
            results.append(tuple(prefix))
            return
        if j == 1:
            candidates = [a[0]]
        else:
            hi = (a[j - 1] * prefix[-1]) // a[j - 2]
            candidates = range(0, hi + 1)
        for v in candidates:
            rec(prefix + [v])

    rec([])
    return results


def lovasz_curve(n, x):
    """
    gamma(x) = (binomial(x,1),...,binomial(x,n)) in R^n, x real -- the
    Lovasz real-binomial extension used in the "continuous" Kruskal-Katona
    bound. For x = 1,...,n integer this hits exactly the Kozlov-simplex
    vertices v_1,...,v_n. Exploratory (2026-08-02, speculative KK/binomial-
    basis connection, see right-angle-simplices-notes.md): T(kozlov_vector(n))
    * gamma(x) always sums to x/n (same linear identity as for f-vectors,
    holds for any vector), but has NEGATIVE entries for non-integer x in
    (1,n) -- so this naive curve is not simply "the path along the simplex
    boundary between consecutive v_i", it leaves the density-monotone
    (nonneg-binomial-coordinate) region between skeleton vertices.
    """
    return [binomial(x, i) for i in range(1, n + 1)]


def lattice_image_condition_a(a, y, tol=1e-9):
    """
    Check the necessary-and-sufficient condition (derived 2026-08-02) for
    y in the standard simplex Delta^(n-1) to be T(a)*x for some integer
    lattice point x in right_angle_simplex(a): writing tailsum_j(y) =
    y_j + y_{j+1} + ... + y_n, require a_j * tailsum_j(y) in Z for every
    j=1,...,n (equivalently x = S(a)*y is an integer vector).
    """
    a = list(a)
    n = len(a)
    tail = QQ(0)
    for j in range(n - 1, -1, -1):
        tail += QQ(y[j])
        val = QQ(a[j]) * tail
        if val.denominator() != 1:
            return False
    return True


def worked_example_n4_d2_ones():
    """
    Prints S(a), T(a), N^d, and B_d = T(a)*N^d*S(a) for the concrete worked
    example n=4, d=2, a=(1,1,1,1) (2026-08-02 session, shown by hand and
    cross-checked in chat before being added here). Since a is all-ones,
    S(a) is literally the all-ones upper-triangular matrix U and T(a)=U^-1
    is the plain backward-difference matrix -- the simplest nontrivial
    instance of the general-a closed form (formula_a's c_i are all 0 or 1
    here). Returns (S, T, Nd, B) as Sage matrices for reuse/further checks.
    """
    a = [1, 1, 1, 1]
    n, d = 4, 2
    S = S_matrix_a(a)
    T = S.inverse()
    Nd = shift_matrix_standard(n, d)
    B_direct = T * Nd * S
    B_formula = shift_matrix_binomial_formula_a(a, d)
    assert B_direct == B_formula, "direct conjugation and closed form disagree"
    print('S(a) ='); print(S)
    print('T(a) ='); print(T)
    print('N^2 ='); print(Nd)
    print('B_2 = T(a) N^2 S(a) ='); print(B_direct)
    return S, T, Nd, B_direct


def verify_against_jts_forskning_note():
    """
    Cross-checks shift_matrix_binomial_formula_a against an INDEPENDENT,
    earlier derivation of the same question, found 2026-08-02 in
    jts-forskning/projekt/exteriorconvex/exteriorconvex.tex (migrated
    verbatim into this project as ../artefacts/exterior-convex.tex; see
    ../artefacts/binomial-basis-shift-crosscheck.typ for the full writeup).

    That note uses different notation (0-indexed weight vector c_0,...,c_N,
    n=N+1) for the same setup: basis vectors f_k = proj_k(c), matrix of
    shift^d in that basis. Its N=5, d=2 worked example gives an explicit
    6x6 matrix with entries symbolic in c_0,...,c_5 (transcribed below
    verbatim from the LaTeX source, NOT from its buggy general-N,d Theorem
    statement just above that example -- that symbolic theorem has a
    transcription error, a literal '-c_0/c_3' where the pattern needs
    '-c_0/c_d', not reproduced here).

    Evaluated at generic, pairwise-distinct a = c = (2,3,5,7,11,13) (chosen
    so no coincidental cancellation could hide a disagreement), this
    project's formula and the old note's worked example agree exactly,
    entry for entry -- confirmed here programmatically, not just by eye.
    Returns True (and raises AssertionError on any mismatch, printing the
    offending entry) rather than silently passing.
    """
    a = [QQ(2), QQ(3), QQ(5), QQ(7), QQ(11), QQ(13)]  # a_1..a_6 = c_0..c_5
    d = 2
    c = a  # alias matching the old note's variable name, same values

    # exterior-convex.tex's explicit N=5, d=2 worked-example matrix,
    # transcribed row by row (0-indexed rows/cols 0..5, matching the LaTeX).
    old_note_B2 = matrix(QQ, [
        [0, 0, 0, 0, 0, 0],
        [-c[0] / c[2]] * 6,
        [c[0] / c[2]] + [c[0] / c[2] - c[1] / c[3]] * 5,
        [0, c[1] / c[3]] + [c[1] / c[3] - c[2] / c[4]] * 4,
        [0, 0, c[2] / c[4]] + [c[2] / c[4] - c[3] / c[5]] * 3,
        [0, 0, 0] + [c[3] / c[5]] * 3,
    ])

    ours_B2 = shift_matrix_binomial_formula_a(a, d)
    assert ours_B2 == old_note_B2, (
        f"mismatch:\nours=\n{ours_B2}\nold note=\n{old_note_B2}"
    )
    print('Cross-check against jts-forskning/exteriorconvex.tex: MATCH')
    return True


if __name__ in ('__main__', 'sage.all'):
    # `sage binomial_basis.py` sets __name__ to 'sage.all', not '__main__' --
    # a known Sage gotcha (confirmed 2026-08-02: silently skips this block,
    # no error, exit 0). Accept both so `sage binomial_basis.py` actually runs it.
    # Tradeoff: a future script that `load()`s this file from within another
    # `sage script.py` batch run will also trigger this block (harmless
    # extra output, not an error) -- only matters if this file is ever
    # imported as a dependency from such a script rather than run directly.
    ok, bad = verify_shift_formula(8)
    print('shift formula verified for n=2..8, all d:', ok, bad)

    ok_a, bad_a = verify_shift_formula_general_a([
        ([2, 5, 3, 7], 1), ([2, 5, 3, 7], 2), ([2, 5, 3, 7], 3),
        ([3, 1, 4, 1, 5], 2), ([6, 2, 2, 2, 2, 2], 3),
        ([1, 1, 1, 1], 2),
    ])
    print('shift formula verified for generic/all-ones a:', ok_a, bad_a)

    print()
    print('Worked example n=4, d=2, a=(1,1,1,1):')
    worked_example_n4_d2_ones()

    print()
    verify_against_jts_forskning_note()

    # KK enumeration vs brute force, n=4
    bf = brute_force_f_vectors(4)
    kk = set(enumerate_f_vectors(4))
    print('n=4: brute force count =', len(bf), ' KK-recursion count =', len(kk),
          ' match:', bf == kk)
