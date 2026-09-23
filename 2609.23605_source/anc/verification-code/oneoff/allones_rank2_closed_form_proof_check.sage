# allones_rank2_closed_form_proof_check.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Machine check accompanying the PROOF of the all-ones
#               rank-two closed form (Plan item C), written up in
#               working-notes/logconcavity-and-allones-attempt.org.
#
# The proof chain is:  M[i][j] = 1
#   <=> (Minkowski vertex lemma) some phi uniquely maximizes both summands at
#       the chosen vertices
#   <=> (prefix sums, a = ones) some Phi has unique max on W(1)=[1,n] at
#       m(1)=i and on W(2)=[d+1,d+n] at m(2)=d+j
#   <=> (Lemma 0 of strategy-a-attempt.org) the two-summand digraph D is
#       acyclic
#   <=> NOT ( m(2) in W(1)  and  m(1) in W(2)  and  m(1) != m(2) )
#       [at rank two only m(1), m(2) have out-edges, so any cycle is the
#        2-cycle m(1) -> m(2) -> m(1)]
#   <=> NOT ( j <= n-d  and  i >= d+1  and  i-d != j ),
# which with t = i-d, m = n-d and the automatic bounds t <= m, j >= 1 is
# exactly the conjectured form: M=0 iff 1<=t<=m, 1<=j<=m, t != j.
#
# This script verifies three things over n = 3..9 (and n=10,11 for the
# criterion-only part), every d in 0..n:
#   (1) the polyhedral M equals the 2-cycle criterion  (the proof's endpoints);
#   (2) the 2-cycle criterion equals the closed form as displayed;
#   (3) ORIENTATION: index i belongs to the UNSHIFTED summand (shift 0),
#       j to the shifted one (shift d) -- and the transposed reading fails
#       somewhere, so the orientation in the statement is forced, not free.
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools

def verts(d, n, N):
    return [vector(QQ, [0]*d + [1]*k + [0]*(N-d-k)) for k in range(1, n+1)]

def polyhedral_zero_set(n, d):
    N = n + d
    V1 = verts(0, n, N); V2 = verts(d, n, N)
    pts = {(i, j): V1[i-1] + V2[j-1]
           for i in range(1, n+1) for j in range(1, n+1)}
    P = Polyhedron(vertices=list(pts.values()), base_ring=QQ)
    VS = set(tuple(v) for v in P.vertices_list())
    return {(i, j) for (i, j), x in pts.items() if tuple(x) not in VS}

def twocycle_zero_set(n, d):
    # m(1)=i in W(1)=[1,n]; m(2)=d+j in W(2)=[d+1,d+n]
    return {(i, j) for i in range(1, n+1) for j in range(1, n+1)
            if (d+j <= n) and (i >= d+1) and (i != d+j)}

def closed_form_zero_set(n, d):
    m = n - d
    return {(i, j) for i in range(1, n+1) for j in range(1, n+1)
            if 1 <= i-d <= m and 1 <= j <= m and i-d != j}

bad = 0; entries = 0
for n in range(3, 10):
    for d in range(0, n+1):
        Z_poly = polyhedral_zero_set(n, d)
        Z_2cyc = twocycle_zero_set(n, d)
        Z_form = closed_form_zero_set(n, d)
        entries += n*n
        ok1 = (Z_poly == Z_2cyc); ok2 = (Z_2cyc == Z_form)
        if not (ok1 and ok2):
            bad += 1
            print("MISMATCH n=%d d=%d: poly==2cyc %s, 2cyc==form %s"
                  % (n, d, ok1, ok2))
print("polyhedral == 2-cycle == closed form: checked n=3..9, all d, "
      "%d entries, %d mismatches" % (entries, bad))

# criterion == closed form alone is pure combinatorics; push further
bad2 = 0
for n in range(3, 12):
    for d in range(0, n+1):
        if twocycle_zero_set(n, d) != closed_form_zero_set(n, d):
            bad2 += 1
print("2-cycle == closed form, n=3..11 all d: %d mismatches" % bad2)

# orientation: does the TRANSPOSED closed form (i and j swapped) also match?
# If it fails somewhere, the orientation in the statement is forced.
diffs = []
for n in range(3, 8):
    for d in range(0, n+1):
        Zt = {(j, i) for (i, j) in closed_form_zero_set(n, d)}
        if Zt != polyhedral_zero_set(n, d):
            diffs.append((n, d))
print("transposed form differs from polyhedral M at %d of the (n,d) tested"
      % len(diffs), "-- e.g.", diffs[:4] if diffs else "(never!)")
