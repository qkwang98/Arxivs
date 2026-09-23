# Changelog (reverse chronological):
# 2026-07-31 20:53 - Claude-Code (agent-shell, no web session): created this file. Generates the
#   3D geometry for a visualization of the n=4, d=1 parameter-space finding (see
#   parameter_space_n4d1.py and ../artefacts/extremal-matrix-general.tex Theorem thm:strong): the
#   normalized simplex a1+a2+a3+a4=1 (ai>0) embedded as a regular tetrahedron in R^3, plus a
#   triangulated mesh of the "wall" surface a2*a4=a3^2 (the sole boundary found separating the two
#   known combinatorial types), plus a point cloud drawn from the already-saved, verified
#   experiment data in ../runs/ (not freshly generated -- reuses the actual computed/labeled
#   points rather than assuming un-checked ones are generic). Pure geometry, no Sage needed.
#
#   The wall surface has a clean explicit parametrization (a2 = a3^2/a4, given a3,a4 free), so no
#   marching-tetrahedra/isosurface-extraction needed -- just grid the (a3,a4) plane, compute a2,
#   keep points with a1=1-a2-a3-a4>0, and triangulate the valid grid.
#
#   Output: ../runs/paramspace_n4_d1_mesh_geometry.json, embedded directly into the visualization
#   artifact (self-contained, no fetch at render time).

"""
Generates 3D geometry (tetrahedron vertices/edges, the a2*a4=a3^2 wall-surface mesh, and a point
cloud drawn from verified experiment data) for visualizing the n=4, d=1 parameter-space
combinatorial-type finding. See parameter_space_n4d1.py for the underlying computational
experiments this visualizes, and ../artefacts/extremal-matrix-general.tex for the proof.

Usage: python3 parameter_space_n4d1_mesh.py   (from the code/ directory; no Sage needed)
"""

import json
import os
import random

OUTDIR = '../runs'

# Regular tetrahedron centered at the origin -- vertex i corresponds to the barycentric axis a_i.
TETRA_VERTICES = [
    (1.0, 1.0, 1.0),
    (1.0, -1.0, -1.0),
    (-1.0, 1.0, -1.0),
    (-1.0, -1.0, 1.0),
]
TETRA_EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def barycentric_to_3d(a):
    """a: (a1,a2,a3,a4) with sum 1 (not required, will be normalized). Returns (x,y,z)."""
    s = sum(a)
    a = [x / s for x in a]
    x = sum(a[i] * TETRA_VERTICES[i][0] for i in range(4))
    y = sum(a[i] * TETRA_VERTICES[i][1] for i in range(4))
    z = sum(a[i] * TETRA_VERTICES[i][2] for i in range(4))
    return (x, y, z)


def wall_surface_mesh(resolution=90, eps=1e-3):
    """
    Triangulated mesh of {a1+a2+a3+a4=1, ai>0, a2*a4=a3^2}, parametrized by free (a3,a4) with
    a2=a3^2/a4, a1=1-a2-a3-a4 (kept only where a1>0). Returns (vertices, triangles) as 3D points
    / index triples.
    """
    grid = {}  # (i,j) -> vertex index, only for valid points
    vertices = []
    for i in range(resolution + 1):
        a3 = eps + (1 - 2 * eps) * i / resolution
        for j in range(resolution + 1):
            a4 = eps + (1 - 2 * eps) * j / resolution
            a2 = a3 * a3 / a4
            a1 = 1 - a2 - a3 - a4
            if a1 > eps and a2 > eps:
                grid[(i, j)] = len(vertices)
                vertices.append(barycentric_to_3d((a1, a2, a3, a4)))

    triangles = []
    for i in range(resolution):
        for j in range(resolution):
            corners = [(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)]
            if all(c in grid for c in corners):
                v00, v10, v01, v11 = (grid[c] for c in corners)
                triangles.append((v00, v10, v11))
                triangles.append((v00, v11, v01))
    return vertices, triangles


def load_point_cloud(n_generic=400, seed=7):
    """
    Reuses already-saved, verified experiment data (parameter_space_n4d1.py's run_grid_experiment
    output) rather than generating fresh unverified points: returns (generic_points, special_points)
    as lists of 3D coordinates, with generic_points thinned to n_generic for a readable scatter
    (special_points -- the ones actually found ON the wall -- kept in full, there are few).
    """
    path = os.path.join(OUTDIR, 'paramspace_n4_d1_grid_K10.json')
    with open(path) as f:
        data = json.load(f)
    generic = [p['a'] for p in data['points'] if p['case'] == 'generic case']
    special = [p['a'] for p in data['points'] if p['case'] == 'special case']
    random.seed(seed)
    generic_sample = random.sample(generic, min(n_generic, len(generic)))
    return (
        [barycentric_to_3d(a) for a in generic_sample],
        [barycentric_to_3d(a) for a in special],
    )


def generate():
    os.makedirs(OUTDIR, exist_ok=True)
    verts, tris = wall_surface_mesh()
    generic_pts, special_pts = load_point_cloud()
    data = {
        '_description': (
            'Precomputed 3D geometry for the n=4,d=1 parameter-space visualization (see '
            '../artefacts/extremal-matrix-general.tex Theorem thm:strong and '
            'parameter_space_n4d1.py). tetra_vertices/tetra_edges: the normalized simplex '
            'a1+a2+a3+a4=1 embedded as a regular tetrahedron, vertex i = axis a_i. '
            'wall_vertices/wall_triangles: triangulated mesh of the a2*a4=a3^2 surface (the sole '
            'boundary found separating the generic combinatorial type from the special/wall '
            'type). generic_points/special_points: a point cloud drawn from the VERIFIED, saved '
            'grid-scan experiment (paramspace_n4_d1_grid_K10.json) -- not freshly generated.'
        ),
        'tetra_vertices': TETRA_VERTICES,
        'tetra_edges': TETRA_EDGES,
        'wall_vertices': verts,
        'wall_triangles': tris,
        'generic_points': generic_pts,
        'special_points': special_pts,
    }
    path = os.path.join(OUTDIR, 'paramspace_n4_d1_mesh_geometry.json')
    with open(path, 'w') as f:
        json.dump(data, f, separators=(',', ':'))
    print(f'wrote {path}: {len(verts)} wall-mesh vertices, {len(tris)} triangles, '
          f'{len(generic_pts)} generic points, {len(special_pts)} special points')
    return path


if __name__ == '__main__':
    generate()
