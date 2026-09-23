# logconcavity_battery.sage
#
# Changelog (reverse chronological):
#   2026-09-06  (later) Added all-pairs diagnostic + concrete witness printout
#               on T3 failure, and two more weakly-log-concave probes (tie-mid,
#               plateau) aimed at the first DEPENDENT parallel link reachable
#               despite jlo=2.
#   2026-09-06  Created. Plan item B (working-notes/PLAN-next-steps-vrep-hrep.org):
#               test whether "Kozlov vector" can be replaced by "strictly
#               log-concave" in the four leg-vector-dependent phenomena, and
#               which direction of slope monotonicity does the work.
#
# For each (leg vector a, shift pattern d) configuration this runs:
#   T1: facets(R) == n*s, s = #distinct shifts.
#   T2: Q_Theta == R (validity+completeness of the Theta-form H-description);
#       on failure, which inclusion breaks.
#   T3 (rank>=3): consecutive-pairs conjunction == extremal tensor T
#       (all-pairs conjunction recorded too).
#   T4: for Theta-link pairs sharing a support pair (c,c+1): dependent vs
#       independent counts, plus the algebraic prediction
#       dependent <=> sigma(c-d(p)) == sigma(c-d(p')), which should hold for
#       EVERY a (it is just proportionality of 2-vectors).
#   T5: rank criterion M[j]=1 <=> rank{tight Theta-normals + e(1)} = N,
#       accuracy over all n^r tuples (only meaningful where T2 passes).
#
# Leg-vector classes (sigma-class COMPUTED, never assumed): Kozlov / all-ones
# controls; strictly log-concave non-binomial (tent i(n+1-i), 2^(i(n-i)),
# random via strictly decreasing slopes); strictly log-convex (reciprocal
# Kozlov, factorials, 2^(i(i-1)/2), random); geometric sigma == 2; weakly
# log-concave with a slope tie; non-monotone sigma (injective and not).
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools
import sys

# ---------- geometry ----------

def verts(a, d, N):
    return [vector(QQ, [0]*d + [a[j] for j in range(k)] + [0]*(N-d-k))
            for k in range(1, len(a)+1)]

def R_of(a, ds):
    n = len(a); N = n + max(ds)
    Vs = [verts(a, d, N) for d in ds]
    pts = [sum(t[1:], t[0]) for t in itertools.product(*Vs)]
    return Polyhedron(vertices=pts, base_ring=QQ)

def theta_conditions(a, ds):
    """The Theta-form system as (name, u, beta) triples meaning u.x >= beta,
    plus the equality x(1)=a(1) handled separately by callers.
    Same rows as kozlov_hrep_theta_form_check.sage's theta_polytope."""
    n = len(a); r = len(ds); N = n + ds[-1]
    def M(p, c):
        return sum(a[c-d-1] for d in ds[p:] if 1 <= c-d <= n)
    cons = []
    def u_of(coeffs):
        return vector(QQ, [coeffs.get(c, 0) for c in range(1, N+1)])
    for p in range(1, r+1):
        d = ds[p-1]
        jlo = 1 if p == 1 else 2
        for j in range(jlo, n):
            c = d + j
            beta = M(p, c)/a[j-1] - M(p, c+1)/a[j]
            cons.append((("I", p, j), u_of({c: 1/a[j-1], c+1: -1/a[j]}), beta))
    for p in range(2, r+1):
        cons.append((("C", p), u_of({ds[p-1]+1: 1}), a[0]))
        c = ds[p-2] + n + 1
        cons.append((("D", p), u_of({c: -1}), -M(p-1, c)))
    cons.append((("F",), u_of({N: 1}), 0))
    return cons

def theta_polytope(a, ds):
    n = len(a); N = n + ds[-1]
    cons = theta_conditions(a, ds)
    ieqs = [[-beta] + list(u) for (nm, u, beta) in cons]
    eqns = [[-a[0]] + [1] + [0]*(N-1)]
    return Polyhedron(ieqs=ieqs, eqns=eqns, base_ring=QQ)

def extremal_support(vertex_lists, N):
    idx = list(itertools.product(*[range(len(v)) for v in vertex_lists]))
    pts = {t: sum((vertex_lists[k][t[k]] for k in range(len(vertex_lists))),
                  vector(QQ, [0]*N)) for t in idx}
    P = Polyhedron(vertices=list(pts.values()), base_ring=QQ)
    V = set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}, pts

# ---------- sigma classification ----------

def sigma_class(a):
    s = [QQ(a[i+1])/QQ(a[i]) for i in range(len(a)-1)]
    dec = all(s[i] > s[i+1] for i in range(len(s)-1))
    inc = all(s[i] < s[i+1] for i in range(len(s)-1))
    wdec = all(s[i] >= s[i+1] for i in range(len(s)-1))
    winc = all(s[i] <= s[i+1] for i in range(len(s)-1))
    inj = (len(set(s)) == len(s))
    if len(s) <= 1:
        cls = "trivial"
    elif dec:   cls = "strict-logconcave"
    elif inc:   cls = "strict-logconvex"
    elif wdec and winc: cls = "geometric"
    elif wdec:  cls = "weak-logconcave"
    elif winc:  cls = "weak-logconvex"
    else:       cls = "nonmonotone"
    return cls, inj, s

# ---------- the battery ----------

def battery(label, a, ds, results):
    a = [QQ(x) for x in a]
    n = len(a); r = len(ds); N = n + max(ds); s_distinct = len(set(ds))
    cls, inj, sig = sigma_class(a)
    R = R_of(a, ds)
    nfac = len([h for h in R.Hrepresentation() if h.is_inequality()])
    t1 = (nfac == n*s_distinct)
    Q = theta_polytope(a, ds)
    t2 = (Q == R)
    t2mode = ""
    if not t2:
        RinQ = all(Q.contains(v.vector()) for v in R.vertices())
        QinR = all(R.contains(v.vector()) for v in Q.vertices())
        t2mode = ("R⊄Q" if not RinQ else "") + ("Q⊄R" if not QinR else "")
        if RinQ and QinR: t2mode = "inclusions hold, unequal?!"
    # T3: consecutive pairwise reduction (rank >= 3)
    t3 = None; t3all = None; t3wit = None
    Vs = [verts(a, d, N) for d in ds]
    T, pts = extremal_support(Vs, N)
    if r >= 3:
        all_pairs = [(p, q) for p in range(r) for q in range(p+1, r)]
        con_pairs = [(p, p+1) for p in range(r-1)]
        pr = {pq: extremal_support([Vs[pq[0]], Vs[pq[1]]], N)[0]
              for pq in all_pairs}
        univ = list(itertools.product(range(n), repeat=r))
        A = {t for t in univ if all((t[p], t[q]) in pr[pq]
                                    for pq in all_pairs for p, q in [pq])}
        C = {t for t in univ if all((t[p], t[q]) in pr[pq]
                                    for pq in con_pairs for p, q in [pq])}
        t3 = (C == T); t3all = (A == T)
        if not t3:
            w = sorted(C - T)[0]   # C >= A >= T always, so C-T nonempty here
            t3wit = (w, w in A)    # witness (0-based), and is it in all-pairs?
    # T4: parallel-support link pairs
    cons = theta_conditions(a, ds)
    links = [(nm, u) for nm, u, beta in cons if nm[0] == "I"]
    supp = {}
    for nm, u in links:
        sp = tuple(i for i, y in enumerate(u) if y != 0)
        supp.setdefault(sp, []).append((nm, u))
    ndep = nind = 0; t4pred = True
    for sp, lst in supp.items():
        for (n1, u1), (n2, u2) in itertools.combinations(lst, 2):
            dep = (matrix(QQ, [u1, u2]).rank() == 1)
            if dep: ndep += 1
            else:   nind += 1
            # algebraic prediction: dep <=> sigma at the two window-local
            # indices agree.  n1=("I",p,j): local index j, slope sigma(j).
            pred = (sig[n1[2]-1] == sig[n2[2]-1])
            if pred != dep: t4pred = False
    # T5: rank criterion accuracy
    e1 = vector(QQ, [1] + [0]*(N-1))
    ok5 = 0
    for t, x in pts.items():
        tight = [u for nm, u, beta in cons if u.dot_product(x) == beta]
        ok5 += ((matrix(QQ, [e1] + tight).rank() == N) == (t in T))
    t5 = (ok5 == n**r)
    row = dict(label=label, a=a, ds=ds, n=n, cls=cls, inj=inj,
               t1=t1, nfac=nfac, pred1=n*s_distinct, t2=t2, t2mode=t2mode,
               t3=t3, t3all=t3all, t3wit=t3wit, ndep=ndep, nind=nind,
               t4pred=t4pred, t5=t5, ok5=ok5, tot5=n**r, sizeT=len(T))
    results.append(row)
    print("%-14s n=%d d=%-10s %-18s inj=%d | T1 %s(f=%d/%d) T2 %s%s T3 %s/all %s "
          "T4 dep=%d ind=%d pred=%s T5 %d/%d |T|=%d%s"
          % (label, n, str(ds), cls, 1 if inj else 0,
             "OK" if t1 else "FAIL", nfac, n*s_distinct,
             "OK" if t2 else "FAIL", ("["+t2mode+"]" if t2mode else ""),
             {None: "--", True: "OK", False: "FAIL"}[t3],
             {None: "--", True: "OK", False: "FAIL"}[t3all],
             ndep, nind, "OK" if t4pred else "FAIL",
             ok5, n**r, len(T),
             ("  T3-witness(0-based)=%s inA=%s" % t3wit) if t3wit else ""))
    sys.stdout.flush()
    return row

# ---------- leg-vector generators ----------

def kozlov(n):   return [binomial(n, j) for j in range(1, n+1)]
def ones(n):     return [1]*n
def tent(n):     return [i*(n+1-i) for i in range(1, n+1)]
def pow2conc(n): return [2**(i*(n-i)) for i in range(1, n+1)]
def kozrecip(n):
    a = kozlov(n); L = lcm(a); return [L//x for x in a]
def factv(n):    return [factorial(i) for i in range(1, n+1)]
def pow2conv(n): return [2**(i*(i-1)//2) for i in range(1, n+1)]
def geom2(n):    return [2**i for i in range(n)]

def rand_strict_logconcave(n, seed):
    # strictly decreasing slopes s_i/t  =>  strictly log-concave
    set_random_seed(seed)
    t = 2
    pool = set()
    while len(pool) < n-1:
        pool.add(ZZ.random_element(1, 40))
    svals = sorted(pool, reverse=True)[:n-1]
    a = [t**(n-1)]
    for i in range(n-1):
        a.append(a[-1]*svals[i]/t)
    return [QQ(x) for x in a]

def rand_strict_logconvex(n, seed):
    a = rand_strict_logconcave(n, seed)
    L = lcm([x.denominator() for x in a])
    a = [x*L for x in a]
    M = lcm([x.numerator() for x in a])
    return [M/x for x in a]   # reciprocal: sigma -> 1/sigma, strictly increasing

def tievec(n):
    # one slope tie at the start, then strictly decreasing: weak log-concave
    if n == 3: return [1, 2, 4]            # sigma = 2,2 (geometric!) -> adjust
    if n == 4: return [1, 2, 4, 6]         # sigma = 2,2,3/2
    if n == 5: return [1, 3, 9, 18, 27]    # sigma = 3,3,2,3/2
    raise ValueError

def nonmono_inj(n):
    if n == 4: return [2, 6, 3, 12]        # sigma = 3,1/2,4  injective
    if n == 5: return [2, 6, 3, 12, 4]     # sigma = 3,1/2,4,1/3 injective
    raise ValueError

def tiemid(n):
    # slope tie placed so two windows at shift gap 1 share a DEPENDENT link:
    # sigma(j) = sigma(j+1) with j >= 2, reachable despite jlo = 2
    if n == 4: return [1, 3, 6, 12]        # sigma = 3,2,2
    if n == 5: return [1, 4, 12, 24, 48]   # sigma = 4,3,2,2
    raise ValueError

def plateau(n):
    # long slope plateau, still weakly log-concave
    if n == 4: return [1, 2, 4, 8]         # geometric at n=4; harmless dup
    if n == 5: return [1, 3, 6, 12, 24]    # sigma = 3,2,2,2
    raise ValueError

def nonmono_noninj(n):
    if n == 4: return [2, 6, 3, 9]         # sigma = 3,1/2,3  non-injective
    if n == 5: return [2, 6, 3, 9, 3]      # sigma = 3,1/2,3,1/3
    raise ValueError

# ---------- driver ----------

results = []
patterns = {2: [[0, 1], [0, 2]],
            3: [[0, 1, 2], [0, 1, 3], [0, 2, 3]],
            4: [[0, 1, 2, 3]]}

def gens_for(n):
    g = [("kozlov", kozlov(n)), ("ones", ones(n)), ("tent", tent(n)),
         ("pow2conc", pow2conc(n)),
         ("rand-lc-1", rand_strict_logconcave(n, 101)),
         ("rand-lc-2", rand_strict_logconcave(n, 202)),
         ("kozrecip", kozrecip(n)), ("fact", factv(n)),
         ("pow2conv", pow2conv(n)),
         ("rand-lx-1", rand_strict_logconvex(n, 303)),
         ("geom2", geom2(n)), ("tie", tievec(n))]
    if n >= 4:
        g += [("nm-inj", nonmono_inj(n)), ("nm-noninj", nonmono_noninj(n)),
              ("tie-mid", tiemid(n)), ("plateau", plateau(n))]
    return g

for n in (3, 4, 5):
    for r in (2, 3, 4):
        if r == 4 and n == 5:
            continue
        for ds in patterns[r]:
            print("\n--- n=%d  d=%s ---" % (n, ds))
            for label, a in gens_for(n):
                battery(label, a, ds, results)

# tie-pattern scope check, separately (Theta-form with tied shifts is
# untested territory even for Kozlov; report, don't mix into the main table)
print("\n=== tied-shift scope check, d=[0,1,1] ===")
tie_results = []
for n in (3, 4):
    for label, a in gens_for(n)[:6]:
        battery(label, a, [0, 1, 1], tie_results)

# ---------- summary ----------

print("\n================ SUMMARY (main battery, no tied shifts) ================")
from collections import defaultdict
agg = defaultdict(lambda: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
# counts: n, t1ok, t2ok, t3run, t3ok, t4predok, t5ok, ndep_total, nind_total, t3allok
for row in results:
    key = (row["cls"], row["inj"])
    A = agg[key]
    A[0] += 1
    A[1] += 1 if row["t1"] else 0
    A[2] += 1 if row["t2"] else 0
    if row["t3"] is not None:
        A[3] += 1
        A[4] += 1 if row["t3"] else 0
        A[9] += 1 if row["t3all"] else 0
    A[5] += 1 if row["t4pred"] else 0
    A[6] += 1 if row["t5"] else 0
    A[7] += row["ndep"]
    A[8] += row["nind"]
print("%-22s %4s | %9s %9s %14s %14s %9s %9s | links dep/ind" %
      ("sigma-class", "inj", "T1 ok", "T2 ok", "T3 ok(consec)", "T3 ok(allpr)",
       "T4 pred", "T5 ok"))
for key in sorted(agg):
    A = agg[key]
    print("%-22s %4s | %6d/%-3d %6d/%-3d %8d/%-5d %8d/%-5d %6d/%-3d %6d/%-3d | %d/%d"
          % (key[0], "yes" if key[1] else "no",
             A[1], A[0], A[2], A[0], A[4], A[3], A[9], A[3], A[5], A[0],
             A[6], A[0], A[7], A[8]))
print("\nFailures in detail (main battery):")
anyfail = False
for row in results:
    fails = [k for k, v in (("T1", row["t1"]), ("T2", row["t2"]),
                            ("T3", row["t3"]), ("T4", row["t4pred"]),
                            ("T5", row["t5"])) if v is False]
    if fails:
        anyfail = True
        print("  %-14s n=%d d=%-10s %-18s a=%s  fails: %s %s"
              % (row["label"], row["n"], str(row["ds"]), row["cls"],
                 row["a"], fails, row["t2mode"]))
if not anyfail:
    print("  (none)")
