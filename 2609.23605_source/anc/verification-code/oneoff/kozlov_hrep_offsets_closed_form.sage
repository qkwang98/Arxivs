# kozlov_hrep_offsets_closed_form.sage -- the offsets in conj-kozlov-hrep2, in closed form.
#
# Changelog (newest first):
#
# 2026-09-13  Created.  The conjecture as printed gave both chains homogeneously and deferred the
#             constants to the phrase "each with the offset forced by additivity"; read literally the
#             display is false -- v_3 + u_3 = (5,10,15,10,10,0,0) in RA(kappa(5);0,2) violates the
#             first chain at j = 2.  Jan asked for the offsets in closed form.  This script derives
#             them from support-function additivity, checks the derivation against direct polyhedral
#             computation, and checks that the resulting H-description cuts out RA exactly.
#
# The claim being tested.  With a_s := 0 for s <= 0 and t = j - d:
#
#   chain 1 at j:   x_j/a_j - x_{j+1}/a_{j+1}  >=  -c_j,   c_j = max(0, a_{t+1}/a_{j+1} - a_t/a_j)
#   chain 2 at j:   x_{d+j}/a_j - x_{d+j+1}/a_{j+1} >= 0       (no offset needed, for THIS a)
#   extras:         x_1 = a_1,   x_{d+1} >= a_1,   x_{n+1} <= a_{m+1},   x_N >= 0
#
# c_j vanishes for j <= d-1 and is positive from j = d on: the shifted copy's leading entry a_1 has
# by then entered the first chain's index window.  Chain 2 needs no offset because the ratios run the
# other way -- see the printed derivation in the article.

def kozvec(n):
    return [binomial(n, j) for j in range(1, n + 1)]          # a_1 .. a_n, 1-indexed via a[j-1]

def ra_vertices(a, n, d, N):
    """Vertex sums of RA(a;0,d) = angle(a) + shift^d angle(a), in R^N."""
    lo = [tuple(a[:p] + [0] * (N - p)) for p in range(1, n + 1)]
    hi = [tuple([0] * d + a[:p] + [0] * (N - d - p)) for p in range(1, n + 1)]
    return [tuple(vector(x) + vector(y)) for x in lo for y in hi]

def entry(a, s):
    """a_s with the convention a_s = 0 for s <= 0 or s > n."""
    return a[s - 1] if 1 <= s <= len(a) else 0

def closed_form_c1(a, n, d, j):
    t = j - d
    if t <= 0 and t + 1 <= 0:
        return QQ(0)
    lead = QQ(entry(a, t + 1)) / entry(a, j + 1) if entry(a, t + 1) else QQ(0)
    trail = QQ(entry(a, t)) / entry(a, j) if entry(a, t) else QQ(0)
    return max(QQ(0), lead - trail)

bad = 0
cases = 0
for n in range(2, 10):
    a = kozvec(n)
    for d in range(1, n):
        N, m = n + d, n - d
        cases += 1
        verts = ra_vertices(a, n, d, N)
        RA = Polyhedron(vertices=verts, base_ring=QQ)

        # --- the offsets, measured directly: c = max over RA of (x_{j+1}/a_{j+1} - x_j/a_j) ---
        for j in range(1, n):
            measured = max(QQ(v[j]) / entry(a, j + 1) - QQ(v[j - 1]) / entry(a, j)
                           for v in verts)
            predicted = closed_form_c1(a, n, d, j)
            if measured != predicted:
                bad += 1
                print("  C1 MISMATCH n=%d d=%d j=%d: measured %s, closed form %s"
                      % (n, d, j, measured, predicted))
            c2 = max(QQ(v[d + j]) / entry(a, j + 1) - QQ(v[d + j - 1]) / entry(a, j)
                     for v in verts)
            if c2 != 0:
                bad += 1
                print("  C2 NONZERO n=%d d=%d j=%d: %s" % (n, d, j, c2))

        # --- the extras, measured ---
        for name, measured, predicted in [
                ("x_1",       min(v[0] for v in verts),     entry(a, 1)),
                ("x_{d+1}>=", min(v[d] for v in verts),     entry(a, 1)),
                ("x_{n+1}<=", max(v[n] for v in verts),     entry(a, m + 1)),
                ("x_N>=",     min(v[N - 1] for v in verts), 0)]:
            if measured != predicted:
                bad += 1
                print("  EXTRA MISMATCH n=%d d=%d %s: measured %s, predicted %s"
                      % (n, d, name, measured, predicted))

        # --- does the closed-form H-description cut out RA exactly? ---
        def row(const, terms):
            v = [QQ(0)] * (N + 1)
            v[0] = QQ(const)
            for idx, coef in terms:
                v[idx] = QQ(coef)
            return v
        ieqs = []
        for j in range(1, n):
            cj = closed_form_c1(a, n, d, j)
            ieqs.append(row(cj, [(j, QQ(1) / entry(a, j)), (j + 1, -QQ(1) / entry(a, j + 1))]))
            ieqs.append(row(0, [(d + j, QQ(1) / entry(a, j)), (d + j + 1, -QQ(1) / entry(a, j + 1))]))
        ieqs.append(row(-entry(a, 1),     [(d + 1, 1)]))          # x_{d+1} >= a_1
        ieqs.append(row(entry(a, m + 1),  [(n + 1, -1)]))         # x_{n+1} <= a_{m+1}
        ieqs.append(row(0,                [(N, 1)]))              # x_N >= 0
        eqns = [row(-entry(a, 1), [(1, 1)])]                      # x_1 = a_1
        cand = Polyhedron(ieqs=ieqs, eqns=eqns, base_ring=QQ)
        if cand != RA:
            bad += 1
            print("  H-DESCRIPTION MISMATCH n=%d d=%d" % (n, d))
        redundant = len(ieqs) - RA.n_facets()
        if redundant != 1:
            print("  NOTE n=%d d=%d: %d of the %d inequalities redundant (facets %d)"
                  % (n, d, redundant, len(ieqs), RA.n_facets()))

print("configurations: %d (n = 2..9, 1 <= d <= n-1).  failures: %d" % (cases, bad))
