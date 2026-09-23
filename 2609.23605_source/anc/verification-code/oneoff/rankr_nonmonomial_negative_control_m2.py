# Changelog (reverse chronological):
# 2026-08-06 23:22 - Claude: created, at Jan's request, as a negative-control
#   companion to rankr_minkowski_random_sampling_m2.py. That experiment only
#   ever samples genuine Amata-Crupi Definition 2.1 monomial submodules
#   (M = I_1 g_1 (+) ... (+) I_r g_r via createModule) -- by construction it
#   can never build a "diagonal"/mixing submodule, so it could never have
#   produced the known n=2, d=(0,0) counterexample M = E.(g_1+g_2) found
#   earlier the same session (see
#   ../artefacts/proper-hilbert-functions-kozlov-minkowski.org section 6).
#   This file deliberately builds several NON-monomial submodules (generators
#   are homogeneous linear combinations mixing multiple free generators, via
#   `image map(F, G, matrix{{...}})`) and checks their real Macaulay2 Hilbert
#   function against ../code/kozlov_minkowski_prediction.py's predicted
#   polytope -- expecting (based on the known counterexample) that at least
#   some land OUTSIDE, demonstrating why the Definition 2.1 restriction is
#   necessary. See ../runs/rank_r_minkowski_experiment_report.md's "Negative
#   control" section for the write-up of what was actually run and found.

"""
Negative-control experiment: does a genuinely non-monomial (non-Definition-2.1)
submodule M of a rank-r free module F ever produce a Hilbert function H_{F/M}
that falls OUTSIDE the polytope predicted by kozlov_minkowski_prediction.py
(the polytope proved, in the org file's section 9, only for M ranging over
genuine monomial submodules M = I_1 g_1 (+) ... (+) I_r g_r)?

Only r=2 is used throughout, following the known counterexample's shape. Each
test case specifies:
  n, degs = (d_1=0, d_2)  -- as usual, degs[0] must be 0 (this project's WLOG
      normalization; predicted_polytope requires it).
  generators : a list of "columns", each column a dict {gen_position (1 or 2):
      monomial} where monomial is a tuple of variable indices (1-indexed;
      () means the constant 1_E). All entries within one column must give the
      same total degree t = degs[pos-1] + len(monomial) -- asserted below --
      since a column is one homogeneous generator of F mixing across
      positions (this is exactly what makes it NON-monomial/non-Definition-2.1:
      a Definition 2.1 generator lives in a single Eg_i, never a sum across i).

The submodule M = image of the resulting matrix map(F, G, mat) (G a free
module with one twisted generator per column, so the map is graded of degree
0) is then handed to hilbertSequence (from Amata-Crupi's ExteriorModules
package, already used and index-convention-checked in
rankr_minkowski_random_sampling_m2.py) exactly as for genuine monomial
submodules -- hilbertSequence M computes H_{F/M} = H_{F / image(mat)}
regardless of whether M happens to be a Definition 2.1 submodule; nothing
about the M2 call cares.
"""

import subprocess
import tempfile
import os
import ast

load('kozlov_minkowski_prediction.py')  # noqa: brings in predicted_polytope


def monomial_to_m2(mono):
    """() -> '1_E' (the ring identity); (i,j,...) -> 'e_i*e_j*...'."""
    if not mono:
        return "1_E"
    return "*".join(f"e_{i}" for i in mono)


def build_matrix_and_source_degrees(n, degs, generators):
    """
    generators: list of columns, each a dict {gen_position (1-indexed): monomial
    tuple}. Returns (m2_matrix_string, source_degrees) where source_degrees is
    a list of -t_j (M2's shift convention, one per column), t_j the column's
    total homogeneous degree.

    Asserts every entry within a column agrees on the column's total degree,
    and that at least two distinct generator positions appear across the
    generators as a whole (a sanity check that this is actually "mixing" and
    not accidentally a monomial submodule in disguise).
    """
    r = len(degs)
    col_degrees = []
    positions_used = set()
    rows = [[] for _ in range(r)]  # rows[i] : list of m2 entry-strings, one per column
    for gens in generators:
        ts = set()
        for pos, mono in gens.items():
            positions_used.add(pos)
            ts.add(degs[pos - 1] + len(mono))
        assert len(ts) == 1, f"column {gens} is not homogeneous: degrees {ts}"
        t = ts.pop()
        col_degrees.append(t)
        for i in range(1, r + 1):
            if i in gens:
                rows[i - 1].append(monomial_to_m2(gens[i]))
            else:
                rows[i - 1].append("0_E")
    assert len(positions_used) >= 2, "not actually a mixing/diagonal generator set"
    matrix_str = "matrix{" + ",".join("{" + ",".join(row) + "}" for row in rows) + "}"
    source_degrees = [-t for t in col_degrees]
    return matrix_str, source_degrees


def _run_m2(script):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".m2", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        out = subprocess.run(["M2", "--script", path], capture_output=True, text=True, timeout=120)
    finally:
        os.unlink(path)
    if out.returncode != 0:
        raise RuntimeError(f"M2 failed:\n{out.stderr}\n--- script ---\n{script}")
    return out.stdout


def _parse_m2_list(text):
    line = text.strip().splitlines()[-1]
    line = line.replace("{", "(").replace("}", ")")
    return ast.literal_eval(line)


def hilbert_sequence_of_nonmonomial_submodule(n, degs, generators):
    """
    Builds F = E^{-d_1,...,-d_r}, M = image map(F, G, mat) for the given
    (non-monomial, mixing) generators, and returns hilbertSequence(M) = H_{F/M}
    as a tuple, computed entirely by Macaulay2.
    """
    matrix_str, source_degrees = build_matrix_and_source_degrees(n, degs, generators)
    degs_m2 = ", ".join(str(-d) for d in degs)
    src_m2 = ", ".join(str(d) for d in source_degrees)
    script = "\n".join([
        'needsPackage "ExteriorModules"',
        f'E = QQ[e_1..e_{n}, SkewCommutative=>true]',
        f'F = E^{{{degs_m2}}}',
        f'G = E^{{{src_m2}}}',
        f'M = image map(F, G, {matrix_str});',
        'print toString hilbertSequence M',
    ])
    raw = _parse_m2_list(_run_m2(script))
    return tuple(raw)


# Test cases: each is (label, n, degs, generators, description).
# generators as documented above. r is always len(degs) == 2 here.
TEST_CASES = [
    (
        "n=2, d=(0,0), g1+g2 [replicates the known counterexample]",
        2, (0, 0),
        [{1: (), 2: ()}],
    ),
    (
        "n=3, d=(0,0), g1+g2 [tied degrees, larger n]",
        3, (0, 0),
        [{1: (), 2: ()}],
    ),
    (
        "n=4, d=(0,0), g1+g2 [tied degrees, even larger n]",
        4, (0, 0),
        [{1: (), 2: ()}],
    ),
    (
        "n=3, d=(0,0), e_1*g1 + e_2*g2 [tied degrees, degree-1 mixing generator]",
        3, (0, 0),
        [{1: (1,), 2: (2,)}],
    ),
    (
        "n=3, d=(0,1), e_1*g1 + g2 [distinct degrees, mixing]",
        3, (0, 1),
        [{1: (1,), 2: ()}],
    ),
    (
        "n=4, d=(0,2), e_1*e_2*g1 + g2 [distinct degrees, larger gap]",
        4, (0, 2),
        [{1: (1, 2), 2: ()}],
    ),
    (
        "n=4, d=(0,3), e_1*e_2*e_3*g1 + g2 [distinct degrees, large gap, high-degree generator]",
        4, (0, 3),
        [{1: (1, 2, 3), 2: ()}],
    ),
    (
        "n=4, d=(0,0), two mixing generators: g1+g2, and e_1*e_2*g1 + e_3*e_4*g2 "
        "[richer multi-generator mixing submodule, tied degrees]",
        4, (0, 0),
        [{1: (), 2: ()}, {1: (1, 2), 2: (3, 4)}],
    ),
]


if __name__ in ('__main__', 'sage.all'):
    print(f"{'label':<90} {'H_F/M':<25} {'inside predicted polytope?'}")
    results = []
    for label, n, degs, generators in TEST_CASES:
        hs = hilbert_sequence_of_nonmonomial_submodule(n, degs, generators)
        target = predicted_polytope(n, degs)
        pt = vector(QQ, hs)
        inside = target.contains(pt)
        results.append((label, n, degs, hs, inside))
        print(f"{label:<90} {str(hs):<25} {'INSIDE' if inside else 'OUTSIDE'}")

    n_outside = sum(1 for r in results if not r[4])
    print(f"\n{n_outside} / {len(results)} test cases landed OUTSIDE the predicted polytope.")
