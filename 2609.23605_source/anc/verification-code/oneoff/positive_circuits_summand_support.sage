# positive_circuits_summand_support.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Strategy B of
#               working-notes/pairwise-reduction-proof-strategies.org:
#               enumerate the POSITIVE CIRCUITS of the Gordan vector
#               configuration {v(p,j(p)) - v(p,l)} in small cases and report
#               how many distinct summands each circuit's support meets.
#
# Background.  M[j] = 1 iff the strict system <phi, v(p,j(p)) - v(p,l)> > 0
# (all p, all l != j(p)) is feasible; by Gordan's theorem it is infeasible iff
# some nontrivial nonnegative combination of the difference vectors vanishes.
# The support-minimal such combinations are the positive circuits of the
# configuration; they are exactly the extreme rays of the cone
#     C = { lambda >= 0 : sum_e lambda_e u_e = 0 },
# equivalently (after normalizing sum lambda = 1) the vertices of a polytope,
# which is how they are enumerated here.
#
# Question (from the note, Strategy B): does every positive circuit meet at
# most two summands -- and at most two ADJACENT summands?  If yes, that is the
# general-a mechanism of the pairwise reduction.  If no, report the
# counterexample and the weaker statistic that actually matters for the
# reduction: whenever ANY positive circuit exists, does one exist meeting
# <= 2 (adjacent) summands?
#
# Cross-checks built in: "some positive circuit exists" must coincide with
# infeasibility, i.e. with NOT-vertex in the polyhedral computation
# (extremal_support, as in consecutive_pairs_determine_extremal_tensor.sage).
#
# RESULT (run 2026-09-06, jts-pc; 32 configurations, both a's, n=3,4, r=3,4,
# 2192 infeasible j-tuples in total):
#   * gordan mismatches: 0 -- positive-circuit existence coincides exactly
#     with polyhedral infeasibility in every case.  (Cross-validation.)
#   * The STRONG guess is FALSE: positive circuits meeting 3 and even 4
#     summands occur for BOTH a = ones and a = kozlov.  For ones they are
#     exactly the directed simple cycles of the prefix-sum digraph (always
#     one vector per summand met: histogram entries only (2,2),(3,3),(4,4)).
#     For kozlov at n = 4 there are additionally FAT circuits using two
#     vectors from one summand, e.g. n=4 r=3 d=[0,1,2], j=(0,3,0):
#     support {(1,1): 3/5, (2,1): 1/4, (2,2): 3/20} -- 2 summands, 3 vectors.
#     (At n = 3 kozlov all circuits are thin; fatness needs n >= 4.)
#   * The WEAK form -- the one equivalent to the pairwise reduction -- holds
#     without exception: EVERY infeasible j has some positive circuit meeting
#     at most 2 summands, and indeed at most 2 ADJACENT summands (0 lacking,
#     in all 32 configurations).
# Detailed discussion in working-notes/strategy-a-attempt.org (Strategy B
# section).

import itertools

def summand_vertices(a, d, N):
    return [vector(QQ, [0]*d + [a[j] for j in range(k)] + [0]*(N-d-k))
            for k in range(1, len(a)+1)]

def extremal_support(vertex_lists, N):
    idx = list(itertools.product(*[range(len(v)) for v in vertex_lists]))
    pts = {t: sum((vertex_lists[k][t[k]] for k in range(len(vertex_lists))),
                  vector(QQ, [0]*N))
           for t in idx}
    P = Polyhedron(vertices=list(pts.values()), base_ring=QQ)
    V = set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}

def positive_circuits(vecs):
    r"""vecs: list of vectors u_e.  Returns the list of positive circuits,
    each as a dict {e: coefficient} with all coefficients > 0, normalized to
    sum 1.  These are the vertices of {lambda >= 0, U lambda = 0,
    sum lambda = 1}."""
    E = len(vecs)
    N = len(vecs[0])
    # ieqs: lambda_e >= 0  ->  [0, e_e]
    ieqs = [[0] + [1 if i == e else 0 for i in range(E)] for e in range(E)]
    # eqns: sum_e lambda_e u_e[c] = 0 for each coordinate c; sum lambda = 1
    eqns = [[0] + [vecs[e][c] for e in range(E)] for c in range(N)]
    eqns.append([-1] + [1]*E)
    P = Polyhedron(ieqs=ieqs, eqns=eqns, base_ring=QQ)
    out = []
    for v in P.vertices_list():
        out.append({e: v[e] for e in range(E) if v[e] != 0})
    return out

def run(aname, n, r, ds):
    a = ([binomial(n, j) for j in range(1, n+1)] if aname == "kozlov"
         else [1]*n)
    N = n + max(ds)
    V = [summand_vertices(a, d, N) for d in ds]
    T = extremal_support(V, N)
    # summand-support statistics
    max_summands = 0                 # over all positive circuits, all j
    worst = None                     # a circuit meeting the most summands
    n_infeas = 0
    n_gordan_mismatch = 0            # positive-circuit existence vs. NOT in T
    n_no_pair_circuit = 0            # infeasible j with NO <=2-summand circuit
    n_no_adj_circuit = 0             # infeasible j with NO adjacent-pair circuit
    hist = {}                        # (summand-count, support-size) -> #circuits
    fat = [None]                     # first circuit with more vectors than summands
    for jt in itertools.product(range(n), repeat=r):
        vecs, labels = [], []
        for p in range(r):
            for l in range(n):
                if l != jt[p]:
                    vecs.append(V[p][jt[p]] - V[p][l])
                    labels.append((p, l))
        circuits = positive_circuits(vecs)
        infeas = jt not in T
        if bool(circuits) != infeas:
            n_gordan_mismatch += 1
        if not infeas:
            continue
        n_infeas += 1
        summand_sets = [sorted(set(labels[e][0] for e in c)) for c in circuits]
        for c, ss in zip(circuits, summand_sets):
            # shape statistic: (number of summands met, support size).
            # Equal entries mean the circuit takes exactly ONE difference
            # vector from each summand it meets.
            hist[(len(ss), len(c))] = hist.get((len(ss), len(c)), 0) + 1
            if len(ss) > max_summands:
                max_summands = len(ss)
                worst = (jt, ss, {labels[e]: c[e] for e in c})
            if len(c) > len(ss) and fat[0] is None:
                fat[0] = (jt, ss, {labels[e]: c[e] for e in c})
        if not any(len(ss) <= 2 for ss in summand_sets):
            n_no_pair_circuit += 1
        if not any(len(ss) == 2 and ss[1] == ss[0] + 1 or len(ss) == 1
                   for ss in summand_sets):
            n_no_adj_circuit += 1
    print("  a=%-6s n=%d r=%d d=%-12s infeas=%3d/%-3d gordan-mism=%d "
          "circuits-by-(#summands,#vectors)=%s  infeas-lacking-pair-circuit=%d "
          "lacking-ADJACENT-pair-circuit=%d"
          % (aname, n, r, str(ds), n_infeas, n**r, n_gordan_mismatch,
             dict(sorted(hist.items())), n_no_pair_circuit, n_no_adj_circuit))
    if worst and max_summands >= 3:
        jt, ss, cdict = worst
        print("      example circuit meeting %d summands: j=%s support "
              "{(p,l): coeff} = %s" % (max_summands, jt,
              {k: str(v) for k, v in sorted(cdict.items())}))
    if fat[0] is not None:
        jt, ss, cdict = fat[0]
        print("      FAT circuit (more vectors than summands): j=%s "
              "support = %s" % (jt, {k: str(v) for k, v in sorted(cdict.items())}))
    return n_gordan_mismatch, n_no_pair_circuit, n_no_adj_circuit

# NB: no `if __name__ == "__main__"` guard -- under this machine's Sage a
# .sage script runs with __name__ == "sage.all", so the guard never fires.
def main():
    tot_mism = tot_nopair = tot_noadj = 0
    for aname in ("ones", "kozlov"):
        for (n, r, patterns) in [
                (3, 3, [[0,1,2],[0,1,1],[0,1,3],[0,2,4]]),
                (4, 3, [[0,1,2],[0,1,1],[0,2,3],[0,2,4]]),
                (3, 4, [[0,1,2,3],[0,0,1,1],[0,1,1,2],[0,2,4,6]]),
                (4, 4, [[0,1,2,3],[0,0,1,1],[0,1,1,2],[0,2,4,6]]),
        ]:
            for ds in patterns:
                m, np_, na = run(aname, n, r, ds)
                tot_mism += m; tot_nopair += np_; tot_noadj += na
    print("\nTOTALS: gordan mismatches=%d, infeasible j lacking a "
          "<=2-summand positive circuit=%d, lacking an ADJACENT-pair "
          "circuit=%d" % (tot_mism, tot_nopair, tot_noadj))

main()
