# check_gemini_review_kozlov_hrep.sage
#
# Changelog (reverse chronological):
#   2026-09-05  Created.  Tests the H-representation for a = the Kozlov vector claimed in
#               review-report-snellman-draft4.pdf section 3.2 -- the Gemini/NotebookLM review of
#               article 1 that Jan added in commit f47e97ae, which presents it as a solution to
#               article 1's Open Problem 2 and states it was "verified exhaustively for n <= 6".
#
#               RESULT: it does not reproduce R = angle(a) + shift^d(angle(a)) in ANY of the 14
#               cases n = 3..6, 1 <= d <= n-1.  Two observations:
#                 * the claimed inequality list has n+d+1 members while R has 2n facets, so for
#                   small d it is structurally too short to cut R out at all (n=6, d=1: the
#                   claimed polytope has 8 facets against R's 12);
#                 * even at d = n-1, where the vertex and facet counts coincide, the two
#                   polytopes are still not equal.
#               This is either a wrong formula or a mis-transcription here of the printed one.
#               NOT RESOLVED -- see TODO.md.  Do not cite the claim either way on this evidence.
#
# Run from the project root:  sage code/oneoff/check_gemini_review_kozlov_hrep.sage

# Test the review's claimed H-representation for a = Kozlov vector (report 1, section 3.2)
def angle(a, d, N):
    verts = []
    for k in range(1, len(a)+1):
        w = [0]*N
        for j in range(k): w[d+j] = a[j]
        verts.append(w)
    return Polyhedron(vertices=verts, base_ring=QQ)

def claimed(n, d):
    a = [binomial(n, j) for j in range(1, n+1)]      # a[0]=a_1 ... a[n-1]=a_n
    A = lambda j: a[j-1]                              # 1-indexed
    N = n + d
    ieqs, eqns = [], []
    def row(): return [0]*(N+1)
    e = row(); e[1] = 1; e[0] = -A(1); eqns.append(e)           # x_1 = a_1
    for j in range(2, d+1):                                      # A-only block
        r = row(); r[j-1] = QQ(1)/A(j-1); r[j] = -QQ(1)/A(j); ieqs.append(r)
    r = row(); r[d+1] = 1; r[0] = -A(1); ieqs.append(r)          # x_{d+1} >= a_1
    r = row(); r[d+1] = -1; r[0] = A(1)
    if d >= 1: r[d] = 1
    ieqs.append(r)                                               # x_{d+1} <= x_d + a_1
    for j in range(d+2, n+1):                                    # overlap block
        r = row(); r[j] = -QQ(1)/A(j); r[j-1] = QQ(1)/A(j-1)
        r[0] = QQ(A(j-d-1) + A(j-d)) / QQ(A(j-1)*A(j))
        ieqs.append(r)
    for j in range(n+1, N+1):                                    # B-only block
        r = row(); r[j-1] = QQ(1)/A(j-d-1); r[j] = -QQ(1)/A(j-d); ieqs.append(r)
    r = row(); r[N] = 1; ieqs.append(r)                          # x_N >= 0
    return Polyhedron(ieqs=ieqs, eqns=eqns, base_ring=QQ)

print("  n  d   actual(V,F)   claimed(V,F)   equal?")
bad = 0
for n in range(3, 7):
    for d in range(1, n):
        a = [binomial(n, j) for j in range(1, n+1)]
        N = n + d
        R = angle(a, 0, N) + angle(a, d, N)
        C = claimed(n, d)
        ok = (R == C)
        if ok is not True: bad += 1
        cv = C.n_vertices() if C.is_compact() else "unbdd"
        print("  %d  %d   (%d,%d)        (%s,%s)      %s"
              % (n, d, R.n_vertices(), R.n_facets(), cv, C.n_facets(), ok))
print("\nfailures:", bad)
