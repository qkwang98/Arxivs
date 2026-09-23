# Changelog (reverse chronological):
# 2026-07-31 20:25 - Claude-Code (agent-shell, no web session): added check_strong_converse,
#   verifying Theorem thm:strong in ../artefacts/extremal-matrix-general.tex (the "strong
#   converse": a=ones vs a=Kozlov specifically diverge for EVERY n>=4 and every d with
#   1<=d<=n-3, i.e. m=n-d>=3 -- not just an existence witness like check_divergence_witness
#   below). Checks the same vertex pair (i=d+1,j=3) and its general-d exposability condition
#   a_2*a_{d+3} < a_{d+2}*a_3, which the article proves algebraically holds unconditionally for
#   Kozlov (reduces to -1<n) and never for ones (reduces to 1<1) -- confirms both the matrix
#   entry and, for a spread including larger d, genuine is_combinatorially_isomorphic=False.
# 2026-07-31 20:19 - Claude-Code (agent-shell, no web session): added
#   check_divergence_witness, verifying Proposition prop:divergence in
#   ../artefacts/extremal-matrix-general.tex (existence of a divergent a,a' pair at every m>=3 --
#   the "weak converse" to Theorem thm:facelattice): compares a=ones against a=ones-with-a_3
#   bumped, for d=1, n=m+1, m=3,...,6, confirming both the specific extremal-matrix entry
#   M_{d+1,3} flips 0->1 as predicted by the derived condition a_2*a_4 < a_3^2, and that the
#   resulting polytopes are genuinely combinatorially non-isomorphic (not just a relabeled
#   extremal matrix), with strictly more vertices for the bumped a.
# 2026-07-31 20:09 - Claude-Code (agent-shell, no web session): created this file. Extracted the
#   ad-hoc Sage snippets run interactively while working out Theorem thm:facelattice (full
#   face-lattice a-independence for m=n-d<=2, arbitrary positive a) in
#   ../artefacts/extremal-matrix-general.tex, so the computational confirmation cited in that
#   article's "Computational confirmation" remark is saved/rerunnable rather than living only in
#   chat history. Two functions: check_face_lattice_isomorphism (one (n,d) pair) and
#   sweep_m_threshold (the m=1,2,3 spot-check that originally motivated/confirmed the theorem:
#   True at m=1,2, False at m=3).

"""
Computational verification for the a-independence results in
../artefacts/extremal-matrix-general.tex (Theorem thm:m2, vertex-level, and Theorem
thm:facelattice, full face lattice, both for m=n-d<=2, any two positive vectors a).

Checks Polyhedron.is_combinatorially_isomorphic directly -- a stronger check than comparing
f-vectors alone (matching f-vectors is necessary but not sufficient for combinatorial
isomorphism); this is the check actually cited in that article's "Computational confirmation"
remark.

Usage (from the code/ directory):

    sage -c "load('extremal_matrix_general_verification.py'); sweep_m_threshold()"
"""

load('right_angle_simplex.py')  # noqa -- brings in ones_vector, kozlov_vector,
                                 # right_angle_minkowski_sum


def check_face_lattice_isomorphism(n, d, a1_name='ones', a2_name='kozlov'):
    """
    n, d: parameters of R = angle(a) + shift^d(angle(a)); a1_name, a2_name in {'ones', 'kozlov'}.
    Returns (is_isomorphic, f_vector_1, f_vector_2) for the two choices of a at this (n, d).

    m = n - d is the shared-coordinate-block size in extremal-matrix-general.tex's notation.
    Theorem thm:facelattice there predicts is_isomorphic=True whenever m<=2, for ANY two positive
    a (not just ones/kozlov specifically) -- this function defaults to ones vs. kozlov since
    that's the pair the whole investigation started from (see LOGBOOK.md 2026-07-31), but any two
    a-vectors of length n could be substituted.
    """
    a_by_name = {'ones': ones_vector, 'kozlov': kozlov_vector}
    a1 = a_by_name[a1_name](n)
    a2 = a_by_name[a2_name](n)
    R1 = right_angle_minkowski_sum(a1, [0, d])
    R2 = right_angle_minkowski_sum(a2, [0, d])
    iso = R1.is_combinatorially_isomorphic(R2)
    return bool(iso), R1.f_vector(), R2.f_vector()


def sweep_m_threshold():
    """
    Reproduces the spot-check that confirmed Theorem thm:facelattice and Remark rem:m3 (the m=3
    breakdown) computationally: True at m=1, True at m=2 (three separate (n,d) pairs), False at
    m=3. Prints one line per case; returns a dict {(n,d): is_isomorphic}.
    """
    cases = [
        (6, 5, 'm=1 (known via the disjoint-support Cartesian-product argument)'),
        (5, 3, 'm=2'),
        (6, 4, 'm=2'),
        (7, 5, 'm=2'),
        (6, 3, 'm=3 (expected False -- outside Theorem thm:facelattice\'s hypothesis)'),
    ]
    results = {}
    for n, d, label in cases:
        iso, fv1, fv2 = check_face_lattice_isomorphism(n, d)
        results[(n, d)] = iso
        print(f'n={n} d={d} ({label}): combinatorially isomorphic = {iso}')
        if fv1 != fv2:
            print(f'  f-vectors differ (expected once m>=3): {fv1} vs {fv2}')
    return results


def check_divergence_witness(m_values=(3, 4, 5, 6), K=5, outdir=None):
    """
    Verifies Proposition prop:divergence in ../artefacts/extremal-matrix-general.tex: for each
    m in m_values, sets d=1, n=m+1, compares a=ones against a'=ones with only a'_3 replaced by K
    (K>1). Checks (1) the extremal matrix entry M_{d+1,3} (0-indexed [d][2]) is 0 for a, 1 for a',
    matching the derived feasibility condition a_2*a_4 < a_3^2 (false for ones: 1<1; true for a':
    1<K^2); (2) the two polytopes are NOT combinatorially isomorphic (not just differently
    labeled); (3) a' has strictly more vertices. Prints one line per m; returns True iff every
    check passed for every m.
    """
    all_ok = True
    for m in m_values:
        d = 1
        n = m + d
        a = ones_vector(n)
        a_bump = ones_vector(n)
        a_bump[2] = K  # bump a_3 (0-indexed position 2)

        M = extremal_matrix(a, d)
        M_bump = extremal_matrix(a_bump, d)
        i0, j0 = d, 2  # 0-indexed (i=d+1, j=3)
        entry_ok = (M[i0, j0] == 0) and (M_bump[i0, j0] == 1)

        R = right_angle_minkowski_sum(a, [0, d])
        R_bump = right_angle_minkowski_sum(a_bump, [0, d])
        iso = R.is_combinatorially_isomorphic(R_bump)
        nv, nv_bump = R.n_vertices(), R_bump.n_vertices()

        ok = entry_ok and (not iso) and (nv_bump > nv)
        all_ok = all_ok and ok
        print(f'm={m} n={n} d={d}: M[d+1,3] {M[i0,j0]}->{M_bump[i0,j0]} '
              f'(expect 0->1), n_vertices {nv}->{nv_bump}, '
              f'combinatorially_isomorphic={iso} (expect False) -- {"OK" if ok else "MISMATCH"}')
    return all_ok


def check_strong_converse(n_max=10, isomorphism_spot_check=(
        (4, 1), (5, 2), (6, 3), (7, 1), (7, 4), (8, 1), (8, 5))):
    """
    Verifies Theorem thm:strong in ../artefacts/extremal-matrix-general.tex: for a=ones vs
    a=Kozlov specifically (not an arbitrary bump), the vertex pair (i=d+1, j=3) is extremal for
    Kozlov and never for ones, for EVERY n=4,...,n_max and every valid d=1,...,n-3 (m=n-d>=3) --
    checked via the extremal matrix directly (cheap, exhaustive over this whole range). Separately
    spot-checks genuine is_combinatorially_isomorphic=False (more expensive, so only for the
    (n,d) pairs in isomorphism_spot_check, which deliberately includes larger d values, not just
    d=1). Prints progress; returns True iff every check passed.
    """
    all_ok = True
    print('-- exhaustive extremal-matrix-entry check, n=4..%d, all valid d --' % n_max)
    for n in range(4, n_max + 1):
        for d in range(1, n - 2):  # d = 1, ..., n-3
            a_ones = ones_vector(n)
            a_koz = kozlov_vector(n)
            M_ones = extremal_matrix(a_ones, d)
            M_koz = extremal_matrix(a_koz, d)
            i0, j0 = d, 2  # 0-indexed (i=d+1, j=3)
            ok = (M_ones[i0, j0] == 0) and (M_koz[i0, j0] == 1)
            all_ok = all_ok and ok
            if not ok:
                print(f'  MISMATCH at n={n} d={d}: M_ones={M_ones[i0,j0]} M_koz={M_koz[i0,j0]}')
    print(f'  all n=4..{n_max}, all valid d: {"OK" if all_ok else "SOME MISMATCH -- see above"}')

    print('-- is_combinatorially_isomorphic spot-check (includes larger d, not just d=1) --')
    for n, d in isomorphism_spot_check:
        a_ones, a_koz = ones_vector(n), kozlov_vector(n)
        R1 = right_angle_minkowski_sum(a_ones, [0, d])
        R2 = right_angle_minkowski_sum(a_koz, [0, d])
        iso = R1.is_combinatorially_isomorphic(R2)
        ok = not iso
        all_ok = all_ok and ok
        print(f'  n={n} d={d} m={n-d}: combinatorially_isomorphic={iso} (expect False) -- '
              f'{"OK" if ok else "MISMATCH"}')
    return all_ok
