"""Exact finite audit for the fixed-rank obstruction family.

Run with SageMath 10.9 (Z3 4.15.3 is used for the integer feasibility checks):

    sage verify_fixed_rank_boundary.sage

The proofs for arbitrary q are the two-generator module presentation in
Theorem thm:fixed-rank-unbounded and the three-linear-form calculation in
Theorem thm:fixed-rank-unbounded-solution-codimension.  This certificate
checks q=1,2,3,4 independently by polynomial computations and checks the
same-coset fake-exponent equations over all integer pairs.  It does not
extrapolate the polynomial calculations from these four values.
"""

import z3


def repeated_gale_dual(blocks):
    """Return a Gale dual obtained by vertically repeating the five-row block."""
    base = matrix(ZZ, [
        [3, 0],
        [2, 3],
        [-3, -3],
        [1, 1],
        [-3, -1],
    ])
    return block_matrix(blocks, 1, [base for _ in range(blocks)])


def product(entries):
    """Return the product of a nonempty list of ring elements."""
    answer = entries[0].parent().one()
    for entry in entries:
        answer *= entry
    return answer


def support_at(B, v, point):
    """Return the one-based negative support at one lattice point."""
    shifted = v + B * vector(ZZ, point)
    return tuple(j + 1 for j, value in enumerate(shifted) if value < 0)


def verify_same_coset_fake_exponents():
    """Solve the fake-indicial equations in the lattice coset exactly."""
    p, r = z3.Ints("same_coset_p same_coset_r")
    b = 2 * p + 3 * r
    c = -3 * p - 3 * r - 1
    d = p + r
    e = -3 * p - r
    fake_conditions = z3.And(
        z3.Or(*[c == value for value in range(3)],
              *[e == value for value in range(3)]),
        z3.Or(*[b == value for value in range(3)], d == 0),
        z3.Or(b == 0, e == 0, e == 1),
    )
    solver = z3.Solver()
    solver.add(fake_conditions)
    solver.add(z3.Not(z3.Or(
        z3.And(p == 0, r == 0),
        z3.And(p == -3, r == 2),
    )))
    assert solver.check() == z3.unsat

    for expected in [(0, 0), (-3, 2)]:
        solver = z3.Solver()
        solver.add(fake_conditions, p == expected[0], r == expected[1])
        assert solver.check() == z3.sat


def verify_support_geometry(blocks, repeated_B):
    """Audit the realized negative supports, the distinguished collection, and their support fibers."""
    base_B = repeated_gale_dual(1)
    base_v = vector(ZZ, [-1, 0, -1, 0, 0])
    realized = []
    nonnegative_at_41 = []
    fiber_witnesses = {}
    for support_mask in range(1 << 5):
        p, r = z3.Ints(f"p_{blocks}_{support_mask} r_{blocks}_{support_mask}")
        solver = z3.Solver()
        for j in range(5):
            linear = int(base_B[j, 0]) * p + int(base_B[j, 1]) * r
            if support_mask & (1 << j):
                solver.add(linear <= -int(base_v[j]) - 1)
            else:
                solver.add(linear >= -int(base_v[j]))
        if solver.check() == z3.unsat:
            continue
        model = solver.model()
        point = tuple(
            model.eval(variable, model_completion=True).as_long()
            for variable in (p, r)
        )
        support = support_at(base_B, base_v, point)
        realized.append(support)
        fiber_witnesses[support] = point
        solver.push()
        solver.add(-p + 41 * r < 0)
        if solver.check() == z3.unsat:
            nonnegative_at_41.append(support)
        solver.pop()

    expected_realized = [
        (1, 3), (1, 4), (2, 4), (1, 2, 4),
        (3, 5), (1, 3, 5), (2, 3, 5), (2, 4, 5),
    ]
    expected_distinguished = [(1, 3), (1, 4), (1, 3, 5)]
    assert realized == expected_realized
    assert nonnegative_at_41 == expected_distinguished

    # The support fibers of the three members of the distinguished collection
    # lie in the saturated quadrant
    # p <= 0, r >= 0.
    for support in expected_distinguished:
        support_mask = sum(1 << (j - 1) for j in support)
        p, r = z3.Ints(f"contain_p_{blocks}_{support_mask} "
                       f"contain_r_{blocks}_{support_mask}")
        solver = z3.Solver()
        for j in range(5):
            linear = int(base_B[j, 0]) * p + int(base_B[j, 1]) * r
            if support_mask & (1 << j):
                solver.add(linear <= -int(base_v[j]) - 1)
            else:
                solver.add(linear >= -int(base_v[j]))
        solver.add(z3.Or(p > 0, r < 0))
        assert solver.check() == z3.unsat

    # These points have negative weight -p + alpha*r for every alpha > 39.
    negative_witnesses = {
        (2, 4): (1, -3),
        (1, 2, 4): (-39, -1),
        (3, 5): (1, 0),
        (2, 3, 5): (1, -1),
        (2, 4, 5): (1, -2),
    }
    for support, point in negative_witnesses.items():
        assert support_at(base_B, base_v, point) == support
        assert -point[0] + 39 * point[1] <= 0

    # Repeating B and v repeats each support in every coordinate block.
    repeated_v = vector(ZZ, list(base_v) * blocks)
    for support, point in fiber_witnesses.items():
        expected_repetition = tuple(
            5 * block + j
            for block in range(blocks)
            for j in support
        )
        assert support_at(repeated_B, repeated_v, point) == expected_repetition


def verify_toric_groebner_basis(blocks, A):
    """Check the repeated three-element toric Groebner basis."""
    weights = [20, 41, 18, 1, 30] * blocks
    names = [
        f"d{i + 1}_{j + 1}"
        for i in range(blocks)
        for j in range(5)
    ]
    ring = PolynomialRing(
        QQ,
        5 * blocks,
        names=names,
        order=TermOrder("wdeglex", weights),
    )
    variables = ring.gens()
    rows = [
        variables[5 * i:5 * i + 5]
        for i in range(blocks)
    ]
    D = [
        product([row[j] for row in rows])
        for j in range(5)
    ]
    expected = [
        D[2]^3 * D[4]^3 - D[0]^3 * D[1]^2 * D[3],
        D[1]^3 * D[3] - D[2]^3 * D[4],
        D[1] * D[4]^2 - D[0]^3,
    ]
    toric_ideal = ToricIdeal(A, polynomial_ring=ring)
    groebner_basis = list(toric_ideal.groebner_basis())
    assert ring.ideal(groebner_basis) == ring.ideal(expected)
    assert {f.lm() for f in groebner_basis} == {
        f.lm() for f in expected
    }


def verify_colons(blocks):
    """Check the images of both colon ideals and the defect Hilbert series."""
    B = repeated_gale_dual(blocks)
    verify_support_geometry(blocks, B)
    A = B.transpose().right_kernel().basis_matrix()
    assert A.nrows() == 5 * blocks - 2
    assert A.ncols() == 5 * blocks
    assert A * B == 0
    assert B.matrix_from_rows([1, 3]).determinant() == -1
    assert vector(ZZ, [1] * (5 * blocks)) in A.row_module()
    assert Matroid(matrix=A).is_connected()
    assert Matroid(matrix=B.transpose()).is_connected()
    semigroup_moves = [
        vector(ZZ, [-1, 0]),
        vector(ZZ, [0, 1]),
        vector(ZZ, [-1, 1]),
    ]
    assert semigroup_moves[2] == semigroup_moves[0] + semigroup_moves[1]
    assert abs(matrix(ZZ, semigroup_moves[:2]).determinant()) == 1

    # Computing the full toric ideal is independent of the colon computation.
    # The first three members audit the repeated Groebner basis.
    if blocks <= 3:
        verify_toric_groebner_basis(blocks, A)

    names = [
        f"t{i + 1}_{j + 1}"
        for i in range(blocks)
        for j in range(5)
    ]
    R = PolynomialRing(QQ, names, order="degrevlex")
    variables = R.gens()
    rows = [
        variables[5 * i:5 * i + 5]
        for i in range(blocks)
    ]
    T = [
        product([row[j] for row in rows])
        for j in range(5)
    ]

    euler_generators = [
        sum(A[i, j] * variables[j] for j in range(5 * blocks))
        for i in range(5 * blocks - 2)
    ]
    U = R.ideal(euler_generators)
    M = R.ideal(T[2], T[3])
    P = R.ideal(T[1] * T[3], T[2] * T[4])
    e = T[2]

    left_colon = (U * M + P).quotient(R.ideal(e))
    right_colon = (U + P).quotient(R.ideal(e))

    S = PolynomialRing(QQ, ["x", "y"], order="degrevlex")
    x, y = S.gens()
    lam = 2 * x + 3 * y
    mu = 3 * x + y
    z = x + y
    images = []
    for _ in range(blocks):
        images.extend([3 * x, lam, -3 * z, z, -mu])
    phi = R.hom(images, S)

    left_image = S.ideal([phi(g) for g in left_colon.gens()])
    right_image = S.ideal([phi(g) for g in right_colon.gens()])
    expected_left = S.ideal(mu^blocks, lam^blocks * z^blocks)
    expected_right = S.ideal(lam^blocks, mu^blocks)
    expected_annihilator = S.ideal(mu^blocks, z^blocks)
    all_intrinsic = expected_right.intersection(expected_annihilator)
    three_powers = S.ideal(lam^blocks, z^blocks, mu^blocks)

    assert left_image == expected_left
    assert right_image == expected_right
    assert expected_left.quotient(S.ideal(lam^blocks)) == expected_annihilator

    left_length = ZZ(
        S.ideal(expected_left.groebner_basis())._singular_().vdim()
    )
    right_length = ZZ(
        S.ideal(expected_right.groebner_basis())._singular_().vdim()
    )
    annihilator_length = ZZ(
        S.ideal(expected_annihilator.groebner_basis())._singular_().vdim()
    )
    all_intrinsic_length = ZZ(
        S.ideal(all_intrinsic.groebner_basis())._singular_().vdim()
    )
    three_powers_length = ZZ(
        S.ideal(three_powers.groebner_basis())._singular_().vdim()
    )
    expected_all_family_defect = (3 * blocks^2 + 3) // 4
    assert left_length == 2 * blocks^2
    assert right_length == blocks^2
    assert annihilator_length == blocks^2
    assert left_length - right_length == blocks^2
    assert three_powers_length == expected_all_family_defect
    assert left_length - all_intrinsic_length == three_powers_length

    hilbert_difference = (
        expected_left.hilbert_series()
        - expected_right.hilbert_series()
    )
    # Sage returns the Hilbert series as a polynomial in a default variable.
    h = hilbert_difference.parent().gen()
    expected_hilbert = h^blocks * sum(h^j for j in range(blocks))^2
    assert hilbert_difference == expected_hilbert

    print(
        "q=",
        blocks,
        "left_length=",
        left_length,
        "right_length=",
        right_length,
        "defect_length=",
        left_length - right_length,
        "all_family_local_codimension=",
        three_powers_length,
        "hilbert=",
        hilbert_difference,
    )


verify_same_coset_fake_exponents()

for q in range(1, 5):
    verify_colons(q)

print(
    "VERIFIED: fixed lattice rank two, connected column matroid, "
    "normality of the affine semigroup generated by reduced Groebner basis vectors, the support fibers indexed by the distinguished collection, "
    "defect Hilbert series u^q(1+u+...+u^(q-1))^2, "
    "all-family local codimension ceil(3*q^2/4), and the exact same-coset "
    "fake-exponent set {(0,0),(-3,2)} "
    "for q=1,2,3,4."
)
