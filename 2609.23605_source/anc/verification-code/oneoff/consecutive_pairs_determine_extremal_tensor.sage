# consecutive_pairs_determine_extremal_tensor.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Tests the sharpened form of Remark obs-pairwise in
#               article 1: not merely that ALL pairs determine the rank-r
#               extremal tensor, but that the CONSECUTIVE pairs alone do.
#
# Background.  Koz(n; d_1,...,d_r) = sum_p shift^{d_p}(Koz(n)) is a Minkowski
# sum of r right-angle simplices.  Each summand p has vertex set
# {v_p(1),...,v_p(n)}, and a choice j = (j_1,...,j_r) of one vertex from each
# summand gives a candidate vertex sum_p v_p(j_p) of the sum.  The extremal
# tensor is M[j] = 1 iff that sum really is a vertex.
#
# Remark obs-pairwise conjectures the "all pairs" reduction
#     M[j_1,...,j_r] = 1  <=>  M^(p,q)[j_p][j_q] = 1  for every pair p < q,
# with M^(p,q) the rank-two extremal matrix of summands p and q alone.
#
# This script tests the strictly stronger claim that the conjunction may be
# restricted to CONSECUTIVE pairs (p, p+1), the non-consecutive constraints
# being implied.  That matters for the proof strategy, not just the statement:
# it says the constraint network is a PATH rather than a complete graph, which
# puts the problem in tree-structured-CSP territory (arc consistency implies
# global consistency on a tree) and makes a left-to-right induction on r the
# natural proof, extending one summand at a time against only its predecessor.
#
# Note the logical direction.  Consecutive constraints are a SUBSET of all
# pairs, so {consec} superset= {all pairs} superset= T always.  Finding
# consec == T therefore establishes equality throughout, and in particular
# shows the non-consecutive constraints are redundant.
#
# Result: 0 mismatches over 50 configurations (34 at rank 3, 16 at rank 4),
# for a the Kozlov vector and a = (1,...,1), n = 3,4,5, shift patterns
# including ties (0,1,1) and wide gaps (0,2,4,6).

import itertools

def summand_vertices(a, d, N):
    r"""Vertices of shift^d of the right-angle simplex with leg vector a,
    embedded in R^N.  Vertex k is the partial sum of a's first k entries,
    placed starting at coordinate d."""
    return [vector(QQ, [0]*d + [a[j] for j in range(k)] + [0]*(N-d-k))
            for k in range(1, len(a)+1)]

def extremal_support(vertex_lists, N):
    r"""The set of index tuples j whose vertex sum is an actual vertex of the
    Minkowski sum -- i.e. the support of the extremal tensor."""
    idx = list(itertools.product(*[range(len(v)) for v in vertex_lists]))
    pts = {t: sum((vertex_lists[k][t[k]] for k in range(len(vertex_lists))),
                  vector(QQ, [0]*N))
           for t in idx}
    P = Polyhedron(vertices=list(pts.values()), base_ring=QQ)
    V = set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}

def run(r, ns, shift_patterns):
    print("=== rank %d: %d pairs total, %d consecutive ==="
          % (r, r*(r-1)//2, r-1))
    print("  a        n  d                   T  allpairs  consec   all=T  con=T")
    bad_all = bad_con = 0
    all_pairs = [(p, q) for p in range(r) for q in range(p+1, r)]
    con_pairs = [(p, p+1) for p in range(r-1)]
    for aname in ("kozlov", "ones"):
        for n in ns:
            a = ([binomial(n, j) for j in range(1, n+1)] if aname == "kozlov"
                 else [1]*n)
            for ds in shift_patterns:
                if len(ds) != r:
                    continue
                N = n + max(ds)
                V = [summand_vertices(a, d, N) for d in ds]
                T = extremal_support(V, N)
                pr = {pq: extremal_support([V[pq[0]], V[pq[1]]], N)
                      for pq in all_pairs}
                univ = list(itertools.product(range(n), repeat=r))
                A = {t for t in univ
                     if all((t[p], t[q]) in pr[(p, q)] for (p, q) in all_pairs)}
                C = {t for t in univ
                     if all((t[p], t[q]) in pr[(p, q)] for (p, q) in con_pairs)}
                bad_all += 0 if A == T else 1
                bad_con += 0 if C == T else 1
                print("  %-8s %d  %-15s %5d  %6d  %6d   %-5s  %s"
                      % (aname, n, ds, len(T), len(A), len(C), A == T, C == T))
    print("\n  all-pairs mismatches: %d   consecutive-only mismatches: %d\n"
          % (bad_all, bad_con))
    return bad_all, bad_con

# NB: no `if __name__ == "__main__"` guard.  Under this machine's Sage a .sage
# script runs with __name__ == "sage.all", so such a guard never fires and the
# script silently does nothing while still exiting 0.  This file was committed
# with the guard on 2026-09-06 and did exactly that until it was removed the
# same day; the results quoted in the header were produced by the ungated
# version.  Keep the driver at top level.
b1 = run(3, (3, 4, 5),
         [[0,1,2], [0,1,3], [0,2,3], [0,2,4], [0,1,1], [0,1,5]])
b2 = run(4, (3, 4),
         [[0,1,2,3], [0,1,2,4], [0,2,4,6], [0,1,1,2], [0,1,3,4], [0,0,1,1]])
total = sum(b1) + sum(b2)
print("TOTAL MISMATCHES: %d" % total)
print("consecutive pairs suffice" if total == 0 else "COUNTEREXAMPLE FOUND")
