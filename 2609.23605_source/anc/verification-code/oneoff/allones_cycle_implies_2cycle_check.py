# allones_cycle_implies_2cycle_check.py
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Brute-force verification of Theorems A1 and A2 of
#               working-notes/strategy-a-attempt.org, BEFORE trusting the
#               pencil proofs (house rule: a proof needs independent
#               verification, not a pass).
#
# Setting (all-ones prefix-sum digraph, see
# working-notes/pairwise-reduction-proof-strategies.org, Strategy A):
#   windows W(p) = [d(p)+1, d(p)+n], chosen positions m(p) = d(p)+j(p),
#   digraph D with edges m(p) -> x for x in W(p) \ {m(p)}.
#
# Checks performed (plain Python, no Sage needed -- pure interval combinatorics):
#   1. A1  : D has a cycle  =>  D has a 2-cycle
#            (exhaustive over n, r, sorted d-tuples with d(1)=0, all j-tuples)
#   2. A2  : D has a 2-cycle  =>  D has a 2-cycle at some consecutive pair (p, p+1)
#            (same exhaustive range)
#   3. A1* : the STRONGER arbitrary-interval version the proof appears to give
#            (windows of unequal lengths, unsorted): cycle => 2-cycle.
#            Exhaustive over small interval systems + randomized for larger r.
#   4. A2* : counterexample hunt for the A2 analogue with UNEQUAL lengths
#            (sorted by left endpoint): expect a counterexample, documenting
#            that A2 genuinely needs equal window lengths.
#
# RESULT (run 2026-09-06, jts-pc, python3):
#   equal-length exhaustive: 970944 (n,d,j) configurations, 920611 cyclic
#     A1 violations (cycle, no 2-cycle):         0
#     A2 violations (2-cycle, none consecutive): 0
#   arbitrary-interval exhaustive (r=3, span=6): 35028 configs, 20396 cyclic, 0 violations
#   arbitrary-interval exhaustive (r=4, span=5): 100751 configs, 77052 cyclic, 0 violations
#   arbitrary-interval random: 200000 trials, 85787 cyclic, 0 violations
#   A2* counterexample (unequal lengths): windows=((1,3),(1,4),(2,3)) m=(2,4,3),
#     only 2-cycle is the non-consecutive pair (0,2)  -- so A2 needs equal lengths.
#   ALL A1/A2 CHECKS PASSED.
# Proofs written up in working-notes/strategy-a-attempt.org.

import itertools
import random
import sys


def has_cycle(edges_by_src):
    """Iterative 3-color DFS on dict {src: set(dsts)}. True iff a directed
    cycle exists."""
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {}
    verts = set(edges_by_src)
    for ds in edges_by_src.values():
        verts |= ds
    for v in verts:
        color[v] = WHITE
    for root in verts:
        if color[root] != WHITE:
            continue
        stack = [(root, iter(sorted(edges_by_src.get(root, ()))))]
        color[root] = GRAY
        while stack:
            v, it = stack[-1]
            advanced = False
            for w in it:
                if color[w] == GRAY:
                    return True
                if color[w] == WHITE:
                    color[w] = GRAY
                    stack.append((w, iter(sorted(edges_by_src.get(w, ())))))
                    advanced = True
                    break
            if not advanced:
                color[v] = BLACK
                stack.pop()
    return False


def build_digraph(windows, m):
    """windows: list of (lo, hi) inclusive; m: list of chosen values,
    m[p] in windows[p]. Returns {src: set(dst)}."""
    edges = {}
    for (lo, hi), mp in zip(windows, m):
        s = edges.setdefault(mp, set())
        s.update(x for x in range(lo, hi + 1) if x != mp)
    return edges


def two_cycles(windows, m):
    """List of pairs (p,q), p<q, forming a 2-cycle."""
    out = []
    r = len(windows)
    for p in range(r):
        for q in range(p + 1, r):
            if m[p] == m[q]:
                continue
            (lp, hp), (lq, hq) = windows[p], windows[q]
            if lp <= m[q] <= hp and lq <= m[p] <= hq:
                out.append((p, q))
    return out


def check_equal_length_exhaustive():
    """Checks 1 (A1) and 2 (A2) over the stated exhaustive range."""
    bad_a1 = []
    bad_a2 = []
    n_cfg = n_cyc = 0
    ranges = [(n, r) for n in range(1, 6) for r in range(2, 6)]
    ranges += [(3, 6)]  # one taller case
    for n, r in ranges:
        dmax = n + 1
        for dtail in itertools.combinations_with_replacement(range(dmax + 1),
                                                             r - 1):
            ds = (0,) + dtail          # WLOG d(1)=0, sorted
            windows = [(d + 1, d + n) for d in ds]
            for jt in itertools.product(range(1, n + 1), repeat=r):
                m = [d + j for d, j in zip(ds, jt)]
                n_cfg += 1
                tc = two_cycles(windows, m)
                cyc = has_cycle(build_digraph(windows, m))
                if cyc:
                    n_cyc += 1
                    if not tc:
                        bad_a1.append((n, ds, jt))
                if tc and not any(q == p + 1 for p, q in tc):
                    bad_a2.append((n, ds, jt, tc))
    print("equal-length exhaustive: %d (n,d,j) configurations, %d cyclic"
          % (n_cfg, n_cyc))
    print("  A1 violations (cycle, no 2-cycle):            %d %s"
          % (len(bad_a1), bad_a1[:3]))
    print("  A2 violations (2-cycle, none consecutive):    %d %s"
          % (len(bad_a2), bad_a2[:3]))
    return not bad_a1 and not bad_a2


def check_arbitrary_intervals_exhaustive(span=6, r=3):
    """Check 3 (A1*), exhaustive: all r-tuples of subintervals of [1,span],
    all m-tuples. Unequal lengths, unsorted order both included."""
    intervals = [(lo, hi) for lo in range(1, span + 1)
                 for hi in range(lo, span + 1)]
    bad = []
    n_cfg = n_cyc = 0
    for windows in itertools.combinations_with_replacement(intervals, r):
        # combinations_with_replacement gives lex-sorted systems; order of
        # windows is irrelevant to both "cycle" and "2-cycle", so this loses
        # no generality and saves a factor r!.
        for m in itertools.product(*[range(lo, hi + 1) for lo, hi in windows]):
            n_cfg += 1
            cyc = has_cycle(build_digraph(windows, list(m)))
            if cyc:
                n_cyc += 1
                if not two_cycles(windows, list(m)):
                    bad.append((windows, m))
    print("arbitrary-interval exhaustive (r=%d, span=%d): %d configs, "
          "%d cyclic, A1* violations: %d %s"
          % (r, span, n_cfg, n_cyc, len(bad), bad[:3]))
    return not bad


def check_arbitrary_intervals_random(trials=200000, seed=20260906):
    """Check 3 (A1*), randomized, larger r and spans."""
    rng = random.Random(seed)
    bad = []
    n_cyc = 0
    for _ in range(trials):
        r = rng.randint(2, 6)
        windows = []
        m = []
        for _ in range(r):
            lo = rng.randint(1, 9)
            hi = lo + rng.randint(0, 5)
            windows.append((lo, hi))
            m.append(rng.randint(lo, hi))
        if has_cycle(build_digraph(windows, m)):
            n_cyc += 1
            if not two_cycles(windows, m):
                bad.append((windows, m))
    print("arbitrary-interval random: %d trials, %d cyclic, "
          "A1* violations: %d %s" % (trials, n_cyc, len(bad), bad[:3]))
    return not bad


def hunt_a2_unequal_counterexample():
    """Check 4 (A2*): with unequal lengths, sorted by left endpoint, look for
    a system with a 2-cycle but no CONSECUTIVE 2-cycle. Finding one shows A2
    genuinely uses equal window lengths."""
    span = 7
    intervals = [(lo, hi) for lo in range(1, span + 1)
                 for hi in range(lo, span + 1)]
    for r in (3, 4):
        for windows in itertools.combinations_with_replacement(intervals, r):
            # combinations_with_replacement output is sorted lexicographically,
            # i.e. by left endpoint (ties by right) -- the natural analogue of
            # the sorted-d convention.
            for m in itertools.product(*[range(lo, hi + 1)
                                         for lo, hi in windows]):
                tc = two_cycles(windows, list(m))
                if tc and not any(q == p + 1 for p, q in tc):
                    print("A2* counterexample (unequal lengths): windows=%s "
                          "m=%s 2-cycles=%s" % (windows, m, tc))
                    return True
        print("  (no A2* counterexample at r=%d, span=%d)" % (r, span))
    return False


if __name__ == "__main__":
    ok = True
    ok &= check_equal_length_exhaustive()
    ok &= check_arbitrary_intervals_exhaustive(span=6, r=3)
    ok &= check_arbitrary_intervals_exhaustive(span=5, r=4)
    ok &= check_arbitrary_intervals_random()
    found = hunt_a2_unequal_counterexample()
    print("A2* unequal-length counterexample found: %s" % found)
    print("ALL A1/A2 CHECKS PASSED" if ok else "*** VIOLATIONS FOUND ***")
    sys.exit(0 if ok else 1)
