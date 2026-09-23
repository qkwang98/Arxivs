# kozlov_facets_review_attack.sage
#
# Changelog (reverse chronological):
# 2026-09-06  Created (Claude-Code, adversarial review session). Independent attack on the
#             proofs in working-notes/conj-kozlov-facets-attempt.org. Q_Theta is implemented
#             FROM THE NOTE'S TEXT, deliberately not reusing kozlov_hrep_theta_form_check.sage,
#             so that a text-level error silently corrected in the author's own script would
#             surface here. Tests: (1) Q_Theta == R at corner configurations (n=2, n=7,
#             gap = n-2, gap = n-1, r=5, middle window covered by neighbours);
#             (2) the peel map: y in the simplex, w vanishes below window 2 (the unstated
#             vanishing claim), w satisfies the literal smaller Theta system, and the full
#             peel CASCADE down to r=1 lands in the last summand;
#             (3) literal Q_Theta(a; (delta)) with delta>0 is UNBOUNDED (the induction-wiring
#             gap made concrete);
#             (4) part-3 argmax-set formulas vs. brute force, exposed-face dimensions = N-2,
#             and the specific coverage-wording counterexample (n=4, d=(0,3), p=2, j=3);
#             (5) product structure at gap n-1 vs n-2 (reduction-3 threshold probe).
#
# Run: sage kozlov_facets_review_attack.sage   (driver at top level -- .sage __main__ trap)

import itertools, random

def kozlov_a(n):
    return [binomial(n, i) for i in range(1, n + 1)]

def summand_vertices(n, a, d, Ntot):
    """Vertices of shift^d(angle(a)) in RR^Ntot (1-based coordinate c -> index c-1)."""
    verts = []
    for k in range(1, n + 1):
        v = [0] * Ntot
        for i in range(1, k + 1):
            v[d + i - 1] = a[i - 1]
        verts.append(v)
    return verts

def build_R(n, dvec):
    a = kozlov_a(n)
    Ntot = n + max(dvec)
    Ps = [Polyhedron(vertices=summand_vertices(n, a, d, Ntot), base_ring=QQ) for d in dvec]
    R = Ps[0]
    for P in Ps[1:]:
        R = R + P
    return R, Ps, a, Ntot

def roof(n, a, dvec, p_idx, c):
    """M(p; c) with p given as 0-based index into dvec; sums windows q > p covering c."""
    s = 0
    for q in range(p_idx + 1, len(dvec)):
        loc = c - dvec[q]
        if 1 <= loc <= n:
            s += a[loc - 1]
    return s

def theta_system(n, dvec, Ntot):
    """(eqns, ieqs) for Q_Theta, straight from the note's text.
    Windows dvec strictly increasing; first window's shift may be nonzero (literal reading:
    NO constraints on coordinates below dvec[0]+1 -- that is the point being attacked).
    Sage format: [b, a1..aN] meaning b + a.x >= 0 (or == 0)."""
    a = kozlov_a(n)
    r = len(dvec)
    d1 = dvec[0]
    eqns, ieqs = [], []
    def ei(c):  # 1-based coordinate to coefficient list index
        return c
    # (E) x(d1+1) = a(1)
    row = [0] * (Ntot + 1); row[0] = -a[0]; row[ei(d1 + 1)] = 1
    eqns.append(row)
    # (I;1): Theta(1;c) >= Theta(1;c+1), c = d1+1 .. d1+n-1   [n-1 links]
    # (I;p), p>=2: c = d(p)+2 .. d(p)+n-1                     [n-2 links]
    for p in range(r):
        dp = dvec[p]
        cstart = dp + 1 if p == 0 else dp + 2
        for c in range(cstart, dp + n):
            A = a[c - dp - 1]      # a(c - d(p))
            B = a[c + 1 - dp - 1]  # a(c+1 - d(p))
            Mc  = roof(n, a, dvec, p, c)
            Mc1 = roof(n, a, dvec, p, c + 1)
            # (x(c)-Mc)/A - (x(c+1)-Mc1)/B >= 0, times A*B:
            row = [0] * (Ntot + 1)
            row[0] = -Mc * B + Mc1 * A
            row[ei(c)] = B
            row[ei(c + 1)] = -A
            ieqs.append(row)
    # (C;p), p>=2: x(d(p)+1) >= a(1)
    for p in range(1, r):
        row = [0] * (Ntot + 1); row[0] = -a[0]; row[ei(dvec[p] + 1)] = 1
        ieqs.append(row)
    # (D;p), p>=2: x(d(p-1)+n+1) <= M(p-1; d(p-1)+n+1)
    for p in range(1, r):
        c0 = dvec[p - 1] + n + 1
        row = [0] * (Ntot + 1)
        row[0] = roof(n, a, dvec, p - 1, c0)
        row[ei(c0)] = -1
        ieqs.append(row)
    # (F) x(d(r)+n) >= 0
    row = [0] * (Ntot + 1); row[ei(dvec[-1] + n)] = 1
    ieqs.append(row)
    return eqns, ieqs

def build_Q(n, dvec, Ntot):
    eqns, ieqs = theta_system(n, dvec, Ntot)
    return Polyhedron(eqns=eqns, ieqs=ieqs, base_ring=QQ)

def peel_once(n, dvec, x):
    """Peel the FIRST window of dvec off x (exact rationals). Returns (y, w)."""
    a = kozlov_a(n)
    d1 = dvec[0]
    y = [QQ(0)] * len(x)
    for c in range(d1 + 1, d1 + n + 1):
        th = (x[c - 1] - roof(n, a, dvec, 0, c)) / a[c - d1 - 1]
        tau = max(QQ(0), th)
        y[c - 1] = a[c - d1 - 1] * tau
    w = [x[i] - y[i] for i in range(len(x))]
    return y, w

def check_config(n, dvec, npoints=40, seed=0):
    """Full battery on one configuration. Returns list of failure strings."""
    fails = []
    R, Ps, a, Ntot = build_R(n, dvec)
    Q = build_Q(n, dvec, Ntot)
    # --- (1) polytope identity and facet count
    if not (Q == R):
        fails.append("Q_Theta != R")
    nfac = len([h for h in R.Hrepresentation() if h.is_inequality()])
    if nfac != len(dvec) * n:
        fails.append("facet count %d != r*n = %d" % (nfac, len(dvec) * n))
    if R.dim() != Ntot - 1:
        fails.append("dim R = %d != N-1 = %d" % (R.dim(), Ntot - 1))
    # --- (2) peel cascade on vertices + sampled points
    rng = random.Random(int(seed))
    pts = [vector(QQ, v) for v in R.vertices_list()]
    vlist = R.vertices_list()
    for _ in range(npoints):
        k = rng.randint(2, min(4, len(vlist)))
        picks = rng.sample(vlist, k)
        wts = [QQ(rng.randint(1, 5)) for _ in range(k)]
        tot = sum(wts)
        pts.append(sum((wts[i] / tot) * vector(QQ, picks[i]) for i in range(k)))
    for x in pts:
        cur = list(x)
        for step in range(len(dvec) - 1):
            sub = dvec[step:]
            y, w = peel_once(n, sub, cur)
            # y in the step-th summand?
            if vector(QQ, y) not in Ps[step]:
                fails.append("peel step %d: y not in summand, x=%s" % (step, x)); break
            # w vanishes strictly below the next window (THE UNSTATED CLAIM)
            lo = dvec[step + 1]
            if any(w[c] != 0 for c in range(0, lo)):
                fails.append("peel step %d: w nonzero below window %d, x=%s" % (step, step + 2, x)); break
            # w satisfies the literal smaller Theta system
            Qs = build_Q(n, dvec[step + 1:], Ntot)
            if vector(QQ, w) not in Qs:
                fails.append("peel step %d: w violates smaller Theta system, x=%s" % (step, x)); break
            cur = w
        else:
            # base: remainder must lie in the LAST summand
            if vector(QQ, cur) not in Ps[-1]:
                fails.append("peel base: remainder not in last summand, x=%s" % (x,))
    return fails

# ---------------- driver ----------------

print("=== (3) literal Q_Theta(a;(delta)) with delta>0 is an unbounded cylinder ===")
for (n, delta) in [(3, 1), (3, 2), (4, 3)]:
    Ntot = n + delta
    Qlit = build_Q(n, [delta], Ntot)
    print("  n=%d delta=%d: literal Q_Theta bounded? %s   (simplex is bounded: True)"
          % (n, delta, Qlit.is_compact()))

print()
print("=== (1)+(2) corner-configuration battery ===")
configs = [
    (2, [0, 1]), (2, [0, 1, 2]), (2, [0, 1, 2, 3, 4]),          # n=2, up to r=5
    (3, [0, 1]), (3, [0, 2]), (3, [0, 1, 2]), (3, [0, 2, 4]),
    (3, [0, 1, 3]), (3, [0, 1, 2, 3, 4]),                        # r=5
    (4, [0, 1]), (4, [0, 2]), (4, [0, 3]),                       # gaps 1, n-2, n-1
    (4, [0, 3, 6]), (4, [0, 2, 4]), (4, [0, 1, 4]), (4, [0, 3, 4]),
    (5, [0, 3]), (5, [0, 4]), (5, [0, 4, 8]), (5, [0, 1, 2]),    # middle window covered
    (5, [0, 1, 2, 3]),
    (6, [0, 4]), (6, [0, 5]),
    (7, [0, 1]), (7, [0, 5]), (7, [0, 6]),                       # n=7, gaps 1, n-2, n-1
]
allok = True
for (n, dvec) in configs:
    fails = check_config(n, dvec, npoints=25, seed=hash((n, tuple(dvec))) % 10**6)
    tag = "OK " if not fails else "FAIL"
    if fails:
        allok = False
    print("  n=%d d=%s N=%d: %s %s" % (n, dvec, n + max(dvec), tag, "; ".join(fails)))
print("battery all OK:", allok)

print()
print("=== (4) part-3 argmax formulas vs brute force + face dimensions ===")

def claimed_normals(n, dvec, a, Ntot):
    """The r*n listed normals (items 1-5), as (label, vector) pairs."""
    out = []
    r = len(dvec)
    u = [0] * Ntot; u[2 - 1] = 1
    out.append(("item1 e(2)", vector(QQ, u)))
    for p in range(r):
        dp = dvec[p]
        for j in range(2, n):
            c = dp + j
            u = [QQ(0)] * Ntot
            u[c + 1 - 1] = QQ(1) / a[j]      # 1/a(j+1)
            u[c - 1] = -QQ(1) / a[j - 1]     # -1/a(j)
            out.append(("item2 p=%d j=%d" % (p + 1, j), vector(QQ, u)))
    u = [0] * Ntot; u[Ntot - 1] = -1
    out.append(("item3 -e(N)", vector(QQ, u)))
    for p in range(1, r):
        u = [0] * Ntot; u[dvec[p] + 1 - 1] = -1
        out.append(("item4 p=%d" % (p + 1,), vector(QQ, u)))
    for p in range(1, r):
        u = [0] * Ntot; u[dvec[p - 1] + n + 1 - 1] = 1
        out.append(("item5 p=%d" % (p + 1,), vector(QQ, u)))
    return out

def argmax_set(u, n, a, d, Ntot):
    vals = [u.dot_product(vector(QQ, v)) for v in summand_vertices(n, a, d, Ntot)]
    m = max(vals)
    return set(k + 1 for k in range(n) if vals[k] == m)

def claimed_A(label, n, dvec, p1, j, q0):
    """Claimed argmax set of summand q0 (0-based) for a type-2 normal at window p1 (1-based), local j."""
    dp = dvec[p1 - 1]; dq = dvec[q0]; c = dp + j
    if q0 == p1 - 1:
        return set(range(1, n + 1)) - {j}
    if q0 < p1 - 1:
        l = c - dq
        return set(range(1, min(l - 1, n) + 1)) if l - 1 >= 1 else set(range(1, n + 1))
    l = c - dq
    if l + 1 >= 2:
        return set(range(max(l + 1, 1), n + 1))
    return set(range(1, n + 1))

for (n, dvec) in [(4, [0, 3]), (5, [0, 1]), (2, [0, 1, 2]), (4, [0, 2, 4]), (7, [0, 6]), (3, [0, 1, 2])]:
    R, Ps, a, Ntot = build_R(n, dvec)
    ok = True
    for (label, u) in claimed_normals(n, dvec, a, Ntot):
        # exposed face dimension must be N-2
        h = max(u.dot_product(vector(QQ, v)) for v in R.vertices_list())
        eq = [[-h] + list(u)]
        F = Polyhedron(eqns=eq, ieqs=[], base_ring=QQ).intersection(R)
        if F.dim() != Ntot - 2:
            ok = False
            print("  n=%d d=%s %s: FACE DIM %d != N-2=%d  *** " % (n, dvec, label, F.dim(), Ntot - 2))
        # type-2 argmax formulas vs brute force
        if label.startswith("item2"):
            p1 = int(label.split("p=")[1].split(" ")[0]); j = int(label.split("j=")[1])
            for q0 in range(len(dvec)):
                got = argmax_set(u, n, a, dvec[q0], Ntot)
                want = claimed_A(label, n, dvec, p1, j, q0)
                if got != want:
                    ok = False
                    print("  n=%d d=%s %s summand %d: argmax %s != claimed %s ***"
                          % (n, dvec, label, q0 + 1, sorted(got), sorted(want)))
    print("  n=%d d=%s: argmax formulas + face dims %s" % (n, dvec, "OK" if ok else "MISMATCH"))

print()
print("=== (4b) the coverage-wording slip, concretely: n=4, d=(0,3), item2 p=2 j=3 ===")
n, dvec = 4, [0, 3]
R, Ps, a, Ntot = build_R(n, dvec)
c = dvec[1] + 3
A1 = argmax_set(vector(QQ, [0, 0, 0, 0, QQ(-1)/a[2], QQ(1)/a[3], 0]), n, a, 0, Ntot)
print("  window 1 argmax:", sorted(A1),
      "-> span reaches coordinate", 0 + max(A1), "; but c-1 =", c - 1,
      " (so 'windows q<p cover [2,c-1]' is FALSE here; window p's own lower span must fill in)")

print()
print("=== (5) reduction-3 threshold probe: is R a product at gap n-1? at n-2? ===")
def product_check(n, g):
    dvec = [0, g]
    R, Ps, a, Ntot = build_R(n, dvec)
    # candidate split: coords [1, n] vs [n+1, N] after subtracting the constant a(1)
    # at coordinate d(2)+1 if g = n-1.  Compare facet counts & f-vector against the product.
    P1 = Ps[0]
    # second factor: summand 2 projected to its variable coords
    nfacR = len([h for h in R.Hrepresentation() if h.is_inequality()])
    fR = R.f_vector()
    # product of the two summands as abstract polytopes:
    Pa = Polyhedron(vertices=[v[:n] for v in Ps[0].vertices_list()], base_ring=QQ)
    Pb = Polyhedron(vertices=[v[n:] if g == n - 1 else v[n - 0:] for v in Ps[1].vertices_list()], base_ring=QQ) \
         if g == n - 1 else None
    if g == n - 1:
        prod = Pa * Pb
        same = (prod.f_vector() == fR)
        print("  n=%d gap=%d (n-1): f(R)==f(P1 x P2')? %s   facets(R)=%d, 2n=%d" % (n, g, same, nfacR, 2 * n))
    else:
        print("  n=%d gap=%d (n-2): facets(R)=%d, 2n=%d  (R claimed NOT a product; f-vector %s)"
              % (n, g, nfacR, 2 * n, fR))
for n in [3, 4, 5]:
    product_check(n, n - 1)
    product_check(n, n - 2)

print()
print("done")
