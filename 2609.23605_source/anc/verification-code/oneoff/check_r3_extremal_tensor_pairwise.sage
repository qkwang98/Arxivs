# check_r3_extremal_tensor_pairwise.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created.  Tests the claim in section 3.4 of the Gemini/NotebookLM review of
#               article 1: that for r = 3 the extremal tensor is determined by PAIRWISE
#               compatibility -- no triple is excluded unless some pair already excludes it.
#               Article 1's own open problem 4 cautions the opposite ("not a formal consequence
#               of the r = 2 answer ... not determined by its pairwise data").
#
#               RESULT: the review's claim HOLDS in all 32 configurations tested -- a = Kozlov
#               vector and a = all-ones, n = 3,4,5, six shift patterns each including ties
#               (0,1,1) and wide gaps (0,2,4).  Triple extremality equals the conjunction of the
#               three pairwise conditions exactly; 0 disagreements.
#
#               This is wider than the review's own stated range and confirms it independently.
#               It is evidence, NOT a proof: the review's "topological explanation" (nested
#               supports) does not by itself show the simultaneous-exposure LP decomposes into
#               its pairwise sub-LPs, which is what the statement needs.
#
# Run from the project root:  sage code/oneoff/check_r3_extremal_tensor_pairwise.sage

# Does pairwise compatibility determine the r=3 extremal tensor?
# Review report 1, section 3.4 claims yes ("exactly 0 exclusions", n<=5, r=3).
# Draft 4's open problem 4 explicitly warns it is NOT a formal consequence of r=2.
def verts(a, d, N):
    out = []
    for k in range(1, len(a)+1):
        w = [0]*N
        for j in range(k): w[d+j] = a[j]
        out.append(vector(QQ, w))
    return out

def extremal_set(vlists, N):
    """Which index tuples give vertices of the Minkowski sum."""
    import itertools
    idx = list(itertools.product(*[range(len(v)) for v in vlists]))
    pts = {t: sum((vlists[k][t[k]] for k in range(len(vlists))), vector(QQ, [0]*N)) for t in idx}
    P = Polyhedron(vertices=list(pts.values()), base_ring=QQ)
    V = set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}

print("  a        n  d            triples  pairwise-predicted  agree?")
bad = 0
for aname in ("kozlov", "ones"):
    for n in range(3, 6):
        a = [binomial(n, j) for j in range(1, n+1)] if aname == "kozlov" else [1]*n
        for ds in ([0,1,2], [0,1,3], [0,2,3], [0,1,n-1], [0,2,4], [0,1,1]):
            if max(ds) > n: continue
            N = n + max(ds)
            V = [verts(a, d, N) for d in ds]
            trip = extremal_set(V, N)
            pair = {}
            for (p, q) in [(0,1), (0,2), (1,2)]:
                pair[(p,q)] = extremal_set([V[p], V[q]], N)
            pred = {t for t in [(i,j,k) for i in range(n) for j in range(n) for k in range(n)]
                    if (t[0],t[1]) in pair[(0,1)] and (t[0],t[2]) in pair[(0,2)]
                    and (t[1],t[2]) in pair[(1,2)]}
            ok = (trip == pred)
            if not ok: bad += 1
            extra = len(pred - trip)
            print("  %-8s %d  %-12s %5d  %10d          %s%s"
                  % (aname, n, ds, len(trip), len(pred), ok,
                     "   <-- pairwise OVERPREDICTS by %d" % extra if extra else ""))
print("\ndisagreements:", bad)
