# Changelog (reverse chronological):
# 2026-08-01 - Claude: created this file. Julia/Oscar port of right_angle_simplex.py's
#   "banal" vertex/polytope-construction functions (right_angle_simplex_vertices,
#   right_angle_simplex, shift_vector, shift_polytope, pad_vector, pad_polytope,
#   right_angle_minkowski_sum, ones_vector, kozlov_vector, chain_order_complex_simplex,
#   kozlov_simplex) -- written as a smoke test of the Oscar v1.8.0 install fixed
#   earlier the same day (see ../../LOGBOOK.md's 2026-08-01 08:36 entry: Oscar was
#   silently orphaned under Julia 1.11 after a Fedora julia 1.11->1.12 package
#   upgrade). Deliberately does not port extremal_matrix or the closed-form
#   right_angle_ones_hrepresentation -- those are the actual research content, not
#   "banal" plumbing. Cross-checked against the Sage/Python original for n=4, d=2:
#   same vertex set (as a Set of coordinate tuples), same vertex/facet counts.

"""
Julia/Oscar port of the basic (a-la-carte "banal") functions from
`right_angle_simplex.py` -- see that file's module docstring for the full
mathematical setup (\\angle(a), the shift operator, right-angle simplices).
Ported here only to exercise Oscar's polyhedral-geometry stack
(`convex_hull`, Minkowski sum via `+`, `vertices`) end to end; the
`extremal_matrix` / `right_angle_ones_hrepresentation` research functions are
not replicated.

Oscar note: `convex_hull` takes a matrix with one vertex per *row* (unlike
passing a list of vertex vectors to Sage's `Polyhedron`), and, like Sage,
requires every summand of a Minkowski sum to share the same ambient
dimension -- hence the same `pad_vector`/`pad_polytope` embedding trick as
the Python original.
"""

using Oscar

function _vertices_to_matrix(V::Vector{<:Vector{<:Integer}})
    return reduce(vcat, [permutedims(v) for v in V])
end

"""
    right_angle_simplex_vertices(a)

a: Vector of n positive integers.
Returns [v_1, ..., v_n], v_i = (a_1, ..., a_i, 0, ..., 0) in this specific
order (mirrors the Python version's ordering guarantee).
"""
function right_angle_simplex_vertices(a::Vector{<:Integer})
    n = length(a)
    return [vcat(a[1:i], zeros(Int, n - i)) for i in 1:n]
end

"""
    right_angle_simplex(a)

a: Vector of n positive integers.
Returns the Polyhedron \\angle(a) in R^n spanned by
v_i = (a_1, ..., a_i, 0, ..., 0), i = 1, ..., n.
"""
function right_angle_simplex(a::Vector{<:Integer})
    return convex_hull(_vertices_to_matrix(right_angle_simplex_vertices(a)))
end

"""
    shift_vector(v, d)

v: Vector, a point in R^n. d: non-negative integer.
Returns shift^d(v) = d zeros prepended to v, a point in R^(n+d).
"""
function shift_vector(v::Vector{<:Integer}, d::Integer)
    return vcat(zeros(Int, d), v)
end

"""
    shift_polytope(P, d)

P: Polyhedron in R^n. d: non-negative integer.
Returns shift^d(P), the Polyhedron in R^(n+d) obtained by applying shift^d
to every vertex of P.
"""
function shift_polytope(P::Oscar.Polyhedron, d::Integer)
    V = [Int.(collect(v)) for v in vertices(P)]
    return convex_hull(_vertices_to_matrix([shift_vector(v, d) for v in V]))
end

"""
    pad_vector(v, N)

v: Vector, a point in R^m, m <= N.
Returns v with trailing zeros appended to reach length N.
"""
function pad_vector(v::Vector{<:Integer}, N::Integer)
    return vcat(v, zeros(Int, N - length(v)))
end

"""
    pad_polytope(P, N)

P: Polyhedron in R^m, m <= N.
Returns P embedded in R^N by padding every vertex with trailing zeros.
"""
function pad_polytope(P::Oscar.Polyhedron, N::Integer)
    V = [Int.(collect(v)) for v in vertices(P)]
    return convex_hull(_vertices_to_matrix([pad_vector(v, N) for v in V]))
end

"""
    right_angle_minkowski_sum(a, degs)

a: Vector of n positive integers.
degs: Vector of r non-negative integers d_1, ..., d_r.
Returns the Minkowski sum of shift^{d_i}(right_angle_simplex(a)) for
i = 1, ..., r, embedded in R^N, N = length(a) + maximum(degs).
"""
function right_angle_minkowski_sum(a::Vector{<:Integer}, degs::Vector{<:Integer})
    N = length(a) + maximum(degs)
    P = right_angle_simplex(a)
    summands = [pad_polytope(shift_polytope(P, d), N) for d in degs]
    Q = summands[1]
    for S in summands[2:end]
        Q = Q + S
    end
    return Q
end

"""
    ones_vector(n)

Returns (1, 1, ..., 1), n ones.
"""
ones_vector(n::Integer) = ones(Int, n)

"""
    chain_order_complex_simplex(n)

Returns \\angle(ones_vector(n)) = \\angle(1, ..., 1). See the Python
original's docstring for the (refined, non-trivial) relationship to
Stanley's order polytope O(chain_{n-1}).
"""
chain_order_complex_simplex(n::Integer) = right_angle_simplex(ones_vector(n))

"""
    kozlov_vector(n)

Returns (binom(n,1), binom(n,2), ..., binom(n,n)).
"""
kozlov_vector(n::Integer) = [binomial(n, k) for k in 1:n]

"""
    kozlov_simplex(n)

Returns \\angle(kozlov_vector(n)), confirmed (Python original) against
Kozlov 1997 Theorem 4.1.
"""
kozlov_simplex(n::Integer) = right_angle_simplex(kozlov_vector(n))
