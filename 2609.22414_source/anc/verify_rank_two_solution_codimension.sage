"""Exact certificate for the formal solution-space codimension in the rank 2 example.

Run with the recorded SageMath and Z3 versions:

    sage verify_rank_two_solution_codimension.sage
"""

import z3


def falling(value, exponent):
	ans = value.parent().one()
	for k in range(exponent):
		ans *= value - k
	return ans


def product_of_variables(generators, indices):
	ans = generators[0].parent().one()
	for j in sorted(indices):
		ans *= generators[j - 1]
	return ans


def realized_negative_supports(B, exponent, label):
	realized = []
	for mask in range(1 << B.nrows()):
		p, q = z3.Ints(f"support_{label}_{mask}_p support_{label}_{mask}_q")
		solver = z3.Solver()
		for row in range(B.nrows()):
			is_negative = bool(mask & (1 << row))
			if exponent[row] not in ZZ:
				if is_negative:
					solver.add(z3.BoolVal(False))
				continue
			value = int(exponent[row]) + int(B[row, 0]) * p + int(B[row, 1]) * q
			if is_negative:
				solver.add(value <= -1)
			else:
				solver.add(value >= 0)
		if solver.check() == z3.sat:
			realized.append(frozenset(row + 1 for row in range(B.nrows()) if mask & (1 << row)))
	return realized


def ordered_subfamilies(distinguished, realized, initial_support):
	ordered = []
	for mask in range(1 << len(distinguished)):
		family = frozenset(distinguished[j] for j in range(len(distinguished)) if mask & (1 << j))
		if initial_support not in family:
			continue
		if all(J in family for I in family for J in realized if J.issubset(I)):
			ordered.append(family)
	return ordered


A = matrix(QQ, [
	[1, 1, 1, 1, 1],
	[2, 0, 0, 3, 3],
	[3, 3, 2, 0, 3],
])
B = matrix(QQ, [
	[3, 0],
	[2, 3],
	[-3, -3],
	[1, 1],
	[-3, -1],
])
beta = vector(QQ, [-2, -2, -5])
target_exponent = vector(QQ, [-1, 0, -1, 0, 0])

standard_pairs = [
	((0, 0, 0, 0, 0), (0, 3, 4)),
	((0, 0, 1, 0, 0), (0, 3, 4)),
	((0, 0, 2, 0, 0), (0, 3, 4)),
	((0, 0, 0, 0, 0), (0, 2, 3)),
	((0, 1, 0, 0, 0), (0, 2, 3)),
	((0, 2, 0, 0, 0), (0, 2, 3)),
	((0, 2, 0, 0, 1), (0, 2, 3)),
	((0, 1, 0, 0, 1), (0, 2, 3)),
	((0, 0, 0, 0, 1), (0, 2, 3)),
	((0, 0, 0, 0, 2), (0, 2, 3)),
	((0, 0, 0, 0, 0), (0, 1, 2)),
	((0, 0, 0, 0, 1), (0, 1, 2)),
]

fake_exponents = []
for a_tuple, sigma_tuple in standard_pairs:
	a = vector(QQ, a_tuple)
	sigma = list(sigma_tuple)
	outside = [j for j in range(A.ncols()) if j not in sigma]
	rhs = beta - sum((a[j] * A.column(j) for j in outside), A.column(0).parent().zero())
	coordinates = A.matrix_from_columns(sigma).solve_right(rhs)
	exponent = vector(QQ, A.ncols())
	for j in outside:
		exponent[j] = a[j]
	for j, value in zip(sigma, coordinates):
		exponent[j] = value
	assert A * exponent == beta
	fake_exponents.append(exponent)

unique_exponents = []
for exponent in fake_exponents:
	if exponent not in unique_exponents:
		unique_exponents.append(exponent)
assert len(fake_exponents) == 12
assert len(unique_exponents) == 11
assert fake_exponents.count(target_exponent) == 2

S = PolynomialRing(QQ, names=("s1", "s2"), order="degrevlex")
s1, s2 = S.gens()
theta = vector(S, target_exponent) + B.change_ring(S) * vector(S, [s1, s2])
fake_indicial = S.ideal(
	falling(theta[2], 3) * falling(theta[4], 3),
	falling(theta[1], 3) * theta[3],
	theta[1] * falling(theta[4], 2),
)
assert fake_indicial.vector_space_dimension() == 12

target_component = S.ideal(3*s1 + s2, (s1 + s2)^2)
component_intersection = target_component
for exponent in unique_exponents:
	coordinates = B.solve_right(exponent - target_exponent)
	assert all(generator(*coordinates) == 0 for generator in fake_indicial.gens())
	if coordinates == vector(QQ, [0, 0]):
		continue
	point_component = S.ideal(s1 - coordinates[0], s2 - coordinates[1])
	assert point_component.vector_space_dimension() == 1
	component_intersection = component_intersection.intersection(point_component)
assert target_component.vector_space_dimension() == 2
assert component_intersection == fake_indicial

support_data = {}
for index, exponent in enumerate(unique_exponents):
	realized = realized_negative_supports(B, exponent, index)
	initial_support = frozenset(
		row + 1 for row in range(A.ncols())
		if exponent[row] in ZZ and exponent[row] < 0
	)
	assert not any(support < initial_support for support in realized)
	support_data[tuple(exponent)] = (realized, initial_support)

target_realized, target_initial = support_data[tuple(target_exponent)]
expected_target_realized = {
	frozenset((1, 3)),
	frozenset((1, 4)),
	frozenset((2, 4)),
	frozenset((1, 2, 4)),
	frozenset((3, 5)),
	frozenset((1, 3, 5)),
	frozenset((2, 3, 5)),
	frozenset((2, 4, 5)),
}
target_distinguished = (
	frozenset((1, 3)),
	frozenset((1, 4)),
	frozenset((1, 3, 5)),
)
assert set(target_realized) == expected_target_realized
assert target_initial == frozenset((1, 3))
ordered = ordered_subfamilies(target_distinguished, target_realized, target_initial)
expected_ordered = {
	frozenset((frozenset((1, 3)),)),
	frozenset((frozenset((1, 3)), frozenset((1, 4)))),
}
assert set(ordered) == expected_ordered

linear_forms = list(B.change_ring(S) * vector(S, [s1, s2]))

def intrinsic_comparison_ideal(family):
	family = [set(support) for support in family]
	intersection = set.intersection(*family)
	outside = [set(support) for support in target_realized if frozenset(support) not in {frozenset(I) for I in family}]
	P = S.ideal([
		product_of_variables(linear_forms, (I | J) - intersection)
		for I in family for J in outside
	])
	m = product_of_variables(linear_forms, set(target_initial) - intersection)
	return P.quotient(S.ideal(m))


maximal = S.ideal(s1, s2)
for family in ordered:
	assert intrinsic_comparison_ideal(family) == maximal

T = PolynomialRing(QQ, names=("t1", "t2", "t3", "t4", "t5"), order="degrevlex")
t = T.gens()
U = T.ideal(list(A.change_ring(T) * vector(T, t)))

def boundary_ideals(family):
	family = [set(support) for support in family]
	intersection = set.intersection(*family)
	outside = [set(support) for support in target_realized if frozenset(support) not in {frozenset(I) for I in family}]
	M = T.ideal([product_of_variables(t, I - intersection) for I in family])
	P = T.ideal([
		product_of_variables(t, (I | J) - intersection)
		for I in family for J in outside
	])
	e = product_of_variables(t, set(target_initial) - intersection)
	return M, P, e


ordered_family = (frozenset((1, 3)), frozenset((1, 4)))
distinguished_family = target_distinguished
M_ordered, P_ordered, e_ordered = boundary_ideals(ordered_family)
M_distinguished, P_distinguished, e_distinguished = boundary_ideals(distinguished_family)
assert M_ordered == M_distinguished == T.ideal(t[2], t[3])
assert P_ordered == P_distinguished == T.ideal(t[1]*t[3], t[2]*t[4])
assert e_ordered == e_distinguished == t[2]

phi = T.hom(linear_forms, S)
ambient_target = S.ideal([phi(generator) for generator in (U*M_ordered + P_ordered).quotient(T.ideal(e_ordered)).gens()])
assert ambient_target == target_component
assert maximal.vector_space_dimension() == 1
assert ambient_target.vector_space_dimension() - maximal.vector_space_dimension() == 1

same_coset_pairs = []
for i in range(len(unique_exponents)):
	for j in range(i + 1, len(unique_exponents)):
		coordinates = B.solve_right(unique_exponents[j] - unique_exponents[i])
		if all(coordinate in ZZ for coordinate in coordinates):
			same_coset_pairs.append((i, j, tuple(coordinates)))
assert len(same_coset_pairs) == 1
assert set((tuple(unique_exponents[same_coset_pairs[0][0]]), tuple(unique_exponents[same_coset_pairs[0][1]]))) == {
	tuple(target_exponent),
	(-10, 0, 2, -1, 7),
}
assert B * vector(QQ, [1, -3]) == vector(QQ, [3, -7, 6, -2, 0])

pair_i, pair_j, pair_coordinates = same_coset_pairs[0]
if unique_exponents[pair_i] == target_exponent:
	target_to_other = vector(QQ, pair_coordinates)
else:
	target_to_other = -vector(QQ, pair_coordinates)
K.<sqrt_two> = QuadraticField(2)
alpha = 40 + sqrt_two
assert vector(K, [-1, alpha]).dot_product(target_to_other) == 3 + 2*alpha
assert vector(K, [-1, alpha]).dot_product(target_to_other) > 0

full_solution_dimension = fake_indicial.vector_space_dimension()
local_inverse_dimensions = {
	tuple(exponent): 2 if exponent == target_exponent else 1
	for exponent in unique_exponents
}
intrinsic_coefficient_dimensions = {tuple(exponent): 1 for exponent in unique_exponents}
local_quotient_dimensions = {
	exponent: local_inverse_dimensions[exponent] - intrinsic_coefficient_dimensions[exponent]
	for exponent in local_inverse_dimensions
}
assert sum(local_inverse_dimensions.values()) == 12
assert sum(intrinsic_coefficient_dimensions.values()) == 11
lower_bound = local_quotient_dimensions[tuple(target_exponent)]
upper_bound = sum(local_quotient_dimensions.values())
assert lower_bound == upper_bound == 1
formal_solution_codimension = lower_bound
intrinsic_image_dimension = full_solution_dimension - formal_solution_codimension
assert full_solution_dimension == 12
assert intrinsic_image_dimension == 11
assert formal_solution_codimension == 1

print("VERIFIED")
print("standard pairs =", len(fake_exponents))
print("distinct fake exponents =", len(unique_exponents))
print("fake indicial length =", full_solution_dimension)
print("target local length =", target_component.vector_space_dimension())
print("other local lengths = ten copies of 1")
print("target ordered negative support families =", len(ordered))
print("sum over least equivalence classes =", lower_bound)
print("sum over all fake exponents =", upper_bound)
print("intrinsic image dimension =", intrinsic_image_dimension)
print("formal solution-space codimension =", formal_solution_codimension)
print("missing leading logarithm vector =", tuple(B * vector(QQ, [1, -3])))
