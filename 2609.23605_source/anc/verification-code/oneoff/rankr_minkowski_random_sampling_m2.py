# Changelog (reverse chronological):
# 2026-08-06 22:28 - Claude: created, at Jan's request, as deliverable (b) of
#   the proper-Hilbert-functions independent-check experiment (see
#   ../artefacts/proper-hilbert-functions-kozlov-minkowski.org for the claim
#   being tested, and kozlov_minkowski_prediction.py for deliverable (a), the
#   "prediction" side this file compares against). Builds ACTUAL random
#   monomial submodules and computes their REAL Hilbert function via
#   Macaulay2's own ExteriorModules package (createModule/hilbertSequence),
#   independent of the Kruskal-Katona-based formula used in (a). See
#   ../runs/rank_r_minkowski_experiment_report.md for the write-up of what
#   this was actually run on and what was found.

"""
Deliverable (b): random-sampling experiment via Macaulay2.

For given n and degs = (d_1=0, d_2, ..., d_r): repeatedly builds r random
PROPER monomial ideals I_1, ..., I_r of E = wedge(V_n) (proper: every
generator has degree >= 2, so f_1 = n automatically, matching section 3's
definition -- no filtering needed after the fact), forms F = E^{-d_1,...,-d_r}
and M = createModule({I_1,...,I_r}, F) via Amata-Crupi's ExteriorModules.m2
(already installed system-wide and copied into
../code/amata-crupi_ExteriorModules.m2), and computes hilbertSequence(M) --
the REAL Hilbert function of F/M, computed by Macaulay2 itself, not assumed
from any formula.

Index-convention check (done directly against M2, not assumed): for
F = E^{-d_1,...,-d_r}, hilbertSequence(M) returns H_{F/M}(j) for
j = 0, ..., N (N = n + max(degs)) -- exactly the degree-0-inclusive,
length-(N+1) convention used throughout
../artefacts/proper-hilbert-functions-kozlov-minkowski.org and
kozlov_minkowski_prediction.py, so the two sides can be compared as points in
the SAME R^{N+1} with no translation needed. Verified directly: for n=3,
degs=(0,1), F=E^{0,-1}: hilbertSequence(createModule({ideal(0_E),ideal(0_E)},F))
= {1,4,6,4,1} = H_F itself (M=0), matching H_E(j)+H_E(j-1) computed by hand
for j=0..4 -- confirms the (n+d)+1-entry range starts at ACTUAL degree 0, not
at -max(degs) as a naive reading of hilbertSequence's own M2 source
(`for k from min flatten degrees F to n+max flatten degrees F`) might suggest
(M2's internal `degrees F` for F=E^{0,-1} is {{0},{1}}, i.e. already sign-
flipped relative to the exponents used to build F -- confirmed by direct
`print degrees F`, not just inferred).

Random-ideal generation (Python's `random`, not M2's RNG -- keeps the
combinatorial randomness fully inspectable/reproducible via a seed, while the
actual Hilbert-function COMPUTATION -- the one thing this experiment must not
assume in advance -- is still 100% Macaulay2's). Each of the r ideals is
generated independently per sample by one of three modes (chosen with fixed
weights, see `random_ideal_gens`):

  - zero ideal (M = 0's degree-i summand is everything);
  - "degree on/off": for each degree d = 2..n independently, either ALL
    squarefree monomials of that degree are generators, or none -- a compact
    way to sometimes hit highly structured ideals (including literal skeleton
    ideals, whose quotients are exactly Kozlov's extremal f-vectors) without
    hard-coding them;
  - fully random per-monomial inclusion at a density p drawn uniformly from
    [0.05, 0.95].

This mixes genuinely unstructured sampling (mode 3, the bulk of the intended
"build actual random submodules" test) with a reasonable chance of reaching
the polytope's extreme corners (mode 2) -- without ever hard-coding the
skeleton ideals that are already known (Kozlov's theorem) to be the rank-1
extremal witnesses; see the module-level report for how well this worked in
practice.

M_max heuristic: 30 * (vertex count of the target polytope from (a)), capped
at 400 to keep worst-case wall-clock bounded regardless of how large the
target polytope gets. Reasoning: each of the target's V vertices must be
independently *hit* by some sample (a uniform/structural argument gives no
better than "many trials per vertex" without a much more targeted sampler);
30 trials per vertex is a cheap, generous multiple given M2 batch throughput
here (~50 samples/second, see the report), and the cap keeps any single
(n, d_2) case from dominating total wall-clock if convergence is slow or
impossible.
"""

import itertools
import random
import subprocess
import tempfile
import os
import ast

load('kozlov_minkowski_prediction.py')  # noqa: brings in predicted_polytope


def squarefree_monomials_ge2(n):
    """All squarefree monomials of E = wedge(V_n) of degree >= 2, as sorted
    tuples of variable indices (1-indexed, matching M2's e_1..e_n)."""
    result = []
    for k in range(2, n + 1):
        result.extend(itertools.combinations(range(1, n + 1), k))
    return result


def random_ideal_gens(n, monomials, rng):
    """
    One random selection of generator monomials (a list of tuples, possibly
    empty = zero ideal) for a single ideal I_i of E on n variables, using the
    three-mode scheme documented at module level. `monomials`:
    squarefree_monomials_ge2(n), passed in to avoid recomputing per call.
    """
    mode = rng.random()
    if mode < 0.35:
        return []  # zero ideal
    elif mode < 0.70:
        degrees_on = {d: (rng.random() < 0.5) for d in range(2, n + 1)}
        return [m for m in monomials if degrees_on[len(m)]]
    else:
        p = rng.uniform(0.05, 0.95)
        return [m for m in monomials if rng.random() < p]


def monomial_to_m2(mono):
    return "*".join(f"e_{i}" for i in mono)


def ideal_to_m2(gens):
    if not gens:
        return "ideal(0_E)"
    return "ideal(" + ",".join(monomial_to_m2(m) for m in gens) + ")"


def _run_m2(script):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".m2", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        out = subprocess.run(["M2", "--script", path], capture_output=True, text=True, timeout=180)
    finally:
        os.unlink(path)
    if out.returncode != 0:
        raise RuntimeError(f"M2 failed:\n{out.stderr}\n--- script ---\n{script}")
    return out.stdout


def _parse_m2_nested_list(text):
    line = text.strip().splitlines()[-1]
    line = line.replace("{", "(").replace("}", ")")
    return ast.literal_eval(line)


def m2_batch_hilbert_sequences(n, degs, samples):
    """
    samples: list of tuples-of-gens-lists, one tuple (gens_1, ..., gens_r) per
    sample, len(degs) == r. Returns a list of Hilbert-sequence tuples (length
    N+1, N = n + max(degs)), one per sample, in the same order -- computed by
    a single M2 --script invocation for the whole batch (batching to amortize
    M2 process-startup cost, per the task's explicit ask).
    """
    degs_m2 = ", ".join(str(-d) for d in degs)
    lines = [
        'needsPackage "ExteriorModules"',
        f'E = QQ[e_1..e_{n}, SkewCommutative=>true]',
        f'F = E^{{{degs_m2}}}',
        'results = {};',
    ]
    for gens_tuple in samples:
        ideal_names = []
        for i, gens in enumerate(gens_tuple):
            iname = f"I{i}"
            lines.append(f"{iname} = {ideal_to_m2(gens)};")
            ideal_names.append(iname)
        lines.append(f"M = createModule({{{','.join(ideal_names)}}}, F);")
        lines.append("results = append(results, hilbertSequence M);")
    lines.append("print toString results")
    script = "\n".join(lines)
    raw = _parse_m2_nested_list(_run_m2(script))
    return [tuple(hs) for hs in raw]


def run_experiment(n, degs, batch_size=25, seed=0, verbose=True):
    """
    Top-level driver for a single (n, degs) case. Returns a dict with:
      target            : Polyhedron, the (a)-side prediction
      target_n_vertices : int
      M_max             : int, the heuristic cap used
      converged         : bool
      samples_used      : int (samples actually drawn -- equals M_max iff not converged)
      current_hull      : Polyhedron, conv(all sampled Hilbert sequences)
      missing_vertices  : list of target-vertex tuples never sampled (only meaningful if not converged)
      all_seen          : set of distinct Hilbert-sequence tuples actually observed
    """
    assert degs[0] == 0
    rng = random.Random(int(seed))
    r = len(degs)
    monomials = squarefree_monomials_ge2(n)

    target = predicted_polytope(n, degs)
    v = target.n_vertices()
    M_max = min(30 * v, 400)

    if verbose:
        print(f"=== n={n}, degs={degs}: target has {v} vertices, dim={target.dim()}, "
              f"M_max={M_max} ===")

    current_hull = None
    all_seen = set()
    samples_used = 0
    converged = False

    while samples_used < M_max and not converged:
        this_batch = min(batch_size, M_max - samples_used)
        gens_samples = [tuple(random_ideal_gens(n, monomials, rng) for _ in range(r))
                        for _ in range(this_batch)]
        hs_list = m2_batch_hilbert_sequences(n, degs, gens_samples)

        for hs in hs_list:
            samples_used += 1
            all_seen.add(hs)
            if any(v < 0 for v in hs):
                # Would indicate a serious M2 bug (or a bug here) -- the
                # package has known negative-entry bugs elsewhere (see
                # ../LOGBOOK.md 2026-08-06 20:43) so don't blindly trust an
                # obviously-invalid Hilbert function.
                raise RuntimeError(f"m2 returned a Hilbert sequence with a negative "
                                    f"entry -- do not trust: {hs}")
            pt = vector(ZZ, hs)
            if current_hull is None:
                current_hull = Polyhedron(vertices=[hs])
            elif not current_hull.contains(pt):
                current_hull = Polyhedron(vertices=current_hull.vertices_list() + [list(hs)])

            if current_hull.dim() == target.dim() and current_hull == target:
                converged = True
                break

        if verbose:
            print(f"  ...after {samples_used} samples: hull has "
                  f"{current_hull.n_vertices() if current_hull else 0} vertices "
                  f"(target {v}), converged={converged}")

    missing_vertices = []
    hull_subset_of_target = None
    if not converged:
        target_vs = set(tuple(v_) for v_ in target.vertices_list())
        hull_vs = set(tuple(v_) for v_ in current_hull.vertices_list()) if current_hull else set()
        missing_vertices = sorted(target_vs - hull_vs)
        # Soundness diagnostic, distinct from convergence: does every sampled
        # point still lie WITHIN the predicted polytope (target), even though
        # not every corner of target has been reached yet? If this is ever
        # False, that is a genuine discrepancy (a real Hilbert function
        # falling outside the claimed convex hull) -- much more serious than
        # plain non-convergence, and must be reported prominently.
        hull_subset_of_target = all(target.contains(vector(QQ, pt)) for pt in hull_vs)

    return {
        "n": n, "degs": tuple(degs),
        "target": target, "target_n_vertices": v, "M_max": M_max,
        "converged": converged, "samples_used": samples_used,
        "current_hull": current_hull,
        "missing_vertices": missing_vertices,
        "hull_subset_of_target": hull_subset_of_target,
        "all_seen": all_seen,
    }


if __name__ in ('__main__', 'sage.all'):
    results = []
    for n in (3, 4, 5):
        for d2 in (1, 2, 3):
            res = run_experiment(n, (0, d2), seed=hash((n, d2)) % (2**31))
            results.append(res)
            status = "CONVERGED" if res["converged"] else "DID NOT CONVERGE"
            print(f"n={n}, d2={d2}: {status} after {res['samples_used']} samples "
                  f"(M_max={res['M_max']}, target vertices={res['target_n_vertices']})")
            if not res["converged"]:
                print(f"  missing target vertices: {res['missing_vertices']}")
                print(f"  hull subset of target (soundness check): {res['hull_subset_of_target']}")
            print()
