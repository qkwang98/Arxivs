# Changelog (reverse chronological):
# 2026-07-30 - Claude: ran the SageMath-only functions for the first time
#   (previously untested). Fixed compute_minkowski_sum_volume, which silently
#   returned 0 -- Sage's default .volume() is w.r.t. the ambient space, and
#   this polytope is never full-dimensional there; switched to
#   measure='induced'. Confirmed compute_minkowski_tensor_combinatorial
#   (Method A) disagrees with compute_minkowski_tensor_sage (Method B) and
#   with an independently hand-built Polyhedron whenever the shifted copies'
#   coordinate ranges overlap -- documented as a known bug in its docstring
#   rather than guessed-at, since it reflects a gap in the transcript's own
#   combinatorial argument, not a transcription slip.
# 2026-07-30 - Claude: created this file, extracting and translating (Swedish
#   -> English comments) the Python/SageMath code embedded in
#   ../transcripts/{gemini.md,gemini2.txt,minkowski-gemini.md}; completed the
#   truncated compute_minkowski_tensor_sage by adding the missing final
#   `return M`.

"""
Vertex structure and volume of Minkowski sums of shifted copies of a simplex.

Extracted and translated (Swedish -> English comments) from the Gemini chat
transcripts in ../transcripts/ (gemini.md, gemini2.txt, minkowski-gemini.md).

Setup: P(a) is the simplex in R^(n+1) with vertices
    v_i = (a_0, ..., a_i, 0, ..., 0),   i = 0, ..., n
for a vector a = (a_0, ..., a_n) of positive integers. S^d shifts a vector d
steps to the right (e_m -> e_{m+d}). We study the vertex structure and volume
of the Minkowski sum of r shifted copies

    P(a) + S^{d_1}(P(a)) + ... + S^{d_{r-1}}(P(a))

via the r-dimensional 0/1 tensor M, where M[i_0, ..., i_{r-1}] = 1 iff
v_{i_0} + S^{d_1}(v_{i_1}) + ... + S^{d_{r-1}}(v_{i_{r-1}}) is a true (extreme)
vertex of the sum, rather than a convex combination of other such points.
"""

import numpy as np
import itertools


def verify_conditions(idx_tuple, n, r, shifts):
    """Pure combinatorial check for whether idx_tuple gives a true vertex.

    Builds the tensor without any geometric convex-hull computation, by
    looking for sign contradictions in the normal vector c that would have
    to simultaneously maximize each copy's vertex.

    KNOWN BUG (confirmed by running this against compute_minkowski_tensor_sage
    and against an independent hand-built Sage Polyhedron, 2026-07-30): this
    disagrees with the true vertex set whenever two shifted copies' ambient
    coordinate ranges overlap. Example: n=2, shifts=[0,1], idx_tuple=(0,0) is
    flagged here as a sign conflict (rejected), but (1,1,0,0) is a genuine
    vertex of P((1,1,1)) + S^1(P((1,1,1))) -- confirmed both by
    compute_minkowski_tensor_sage and by direct construction of the Polyhedron
    and inspection of its .vertices(). With non-overlapping shifts (e.g.
    shifts=[0,3] for n=2) this function agrees exactly with the geometric
    method, so the bug is specifically in how overlapping ranges are handled:
    flagging *any* sign disagreement on a shared coordinate as fatal is too
    strict, missing whatever the transcript's own "Villkor 2 (independence at
    the ends)" was meant to capture. Do not trust this function's output when
    shifts overlap (i.e. max(shifts) - min(shifts) <= n); use
    compute_minkowski_tensor_sage instead.
    """
    max_shift = max(shifts)
    ambient_dim = n + 1 + max_shift

    # Requirements on the normal vector c: +1 = positive, -1 = negative, 0 = undetermined
    c_requirements = np.zeros(ambient_dim, dtype=int)

    for m, idx in enumerate(idx_tuple):
        shift = shifts[m]

        # The m-th copy requires a plus sign here
        for k in range(shift, shift + idx + 1):
            if c_requirements[k] == -1:
                return False  # Sign conflict!
            c_requirements[k] = 1

        # The m-th copy requires a minus sign here
        for k in range(shift + idx + 1, shift + n + 1):
            if c_requirements[k] == 1:
                return False  # Sign conflict!
            c_requirements[k] = -1

    return True


def compute_minkowski_tensor_combinatorial(n, r, shifts):
    """Build the 0/1 vertex tensor M using verify_conditions (Method A)."""
    tensor_shape = tuple([n + 1] * r)
    M = np.zeros(tensor_shape, dtype=int)

    for idx_tuple in itertools.product(range(n + 1), repeat=r):
        if verify_conditions(idx_tuple, n, r, shifts):
            M[idx_tuple] = 1

    return M


def compute_minkowski_tensor_sage(n, r, shifts, a_vector=None):
    """Build the 0/1 vertex tensor M by an exact geometric computation in
    SageMath (Method B), using Sage's rational Polyhedron class.

    a_vector defaults to (1, 1, ..., 1) (the order-polytope case); passing an
    explicit a_vector generalizes to an arbitrary simplex P(a).

    Must be run inside a SageMath environment (uses Polyhedron and QQ).
    """
    if a_vector is None:
        a_vector = [1] * (n + 1)

    # Generate the base vertices from the vector a
    base_vertices = []
    for i in range(n + 1):
        v = [0] * (n + 1)
        for k in range(i + 1):
            v[k] = a_vector[k]
        base_vertices.append(v)

    max_shift = max(shifts)
    ambient_dim = n + 1 + max_shift

    # Create the shifted polytopes in Sage (over QQ for exact arithmetic)
    shifted_polytopes = []
    for s in shifts:
        poly_vertices = []
        for v in base_vertices:
            v_shifted = [0] * ambient_dim
            for m in range(n + 1):
                v_shifted[s + m] = v[m]
            poly_vertices.append(v_shifted)
        shifted_polytopes.append(Polyhedron(vertices=poly_vertices, base_ring=QQ))

    # Compute the exact Minkowski sum via Sage's '+' operator
    minkowski_sum = shifted_polytopes[0]
    for P in shifted_polytopes[1:]:
        minkowski_sum = minkowski_sum + P

    true_vertices = set(tuple(int(coord) for coord in vertex) for vertex in minkowski_sum.vertices())

    # Build up the tensor M
    tensor_shape = tuple([n + 1] * r)
    M = np.zeros(tensor_shape, dtype=int)

    for idx_tuple in itertools.product(range(n + 1), repeat=r):
        hypothetical_point = [0] * ambient_dim
        for m, idx in enumerate(idx_tuple):
            s = shifts[m]
            for j in range(n + 1):
                hypothetical_point[s + j] += base_vertices[idx][j]

        if tuple(hypothetical_point) in true_vertices:
            M[idx_tuple] = 1

    return M


def compute_minkowski_sum_volume(n, a, shifts):
    """Build the Minkowski sum P(a) + S^{shifts[1]}(P(a)) + ... exactly in
    Sage and return (dimension, volume) of the resulting polytope.

    The volume is computed with measure='induced': the sum is embedded in an
    ambient space of dimension n+1+max(shifts) but is itself only
    n+len(shifts)-dimensional (one degree of freedom is shared per unit of
    shift overlap), so the plain ambient Lebesgue volume is 0 whenever the
    polytope isn't full-dimensional in its ambient space -- which is always,
    for r>=2 shifted copies. 'induced' gives the volume relative to the
    polytope's own affine hull, matching the "3D-affine volume" the transcript
    describes (confirmed 2026-07-30: reproduces the transcript's claimed
    volume of 1 for n=2, a=(1,1,1), shifts=[0,1], where plain .volume() gives
    0).

    Must be run inside a SageMath environment (uses Polyhedron and QQ).
    """
    # Build the base vertices from the vector a
    base_vertices = []
    for i in range(n + 1):
        v = [0] * (n + 1)
        for k in range(i + 1):
            v[k] = a[k]
        base_vertices.append(v)

    max_shift = max(shifts)
    ambient_dim = n + 1 + max_shift

    # Create the shifted polytopes in Sage
    shifted_polytopes = []
    for s in shifts:
        poly_vertices = []
        for v in base_vertices:
            v_shifted = [0] * ambient_dim
            for m in range(n + 1):
                v_shifted[s + m] = v[m]
            poly_vertices.append(v_shifted)
        shifted_polytopes.append(Polyhedron(vertices=poly_vertices, base_ring=QQ))

    # Compute the Minkowski sum
    minkowski_sum = shifted_polytopes[0]
    for P in shifted_polytopes[1:]:
        minkowski_sum = minkowski_sum + P

    return minkowski_sum.dimension(), minkowski_sum.volume(measure='induced')


if __name__ == "__main__":
    # Example from the transcript: P(1,2,1) + S^1(P(1,2,1)) in R^4
    dimension, volume = compute_minkowski_sum_volume(n=2, a=[1, 2, 1], shifts=[0, 1])
    print(f"Polytope dimension: {dimension}")
    print(f"Exact volume: {volume}")
