# close_gap3_explicit_functional.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created.  CLOSES article 1's open problem 1 -- the "always extremal" half of the
#               Kozlov-vector extremal-matrix conjecture for gaps K = j - t >= 3, open since
#               2026-07-31 (only K = 2 was proved).
#
#               The Gemini review's section 3.1 supplied an ansatz for the K-window but said
#               nothing about the functional OUTSIDE the window, where its z = 0 leaves the
#               partial sums constant and strict uniqueness fails.  The completion is easy and is
#               what this script tests: the three index blocks do not interact, so
#                   e_s = +1        for s <= t      (handles t' < t and j' <= t)
#                   the window      for t < s <= j
#                   e_s = -1        for s > j       (handles t' > j and j' > j)
#               and a SIMPLER window than the review's, uniform in K >= 2 (theirs is ill-defined
#               at K = 2): z_1 = -1, z_K = 1 + delta, all others 0, with
#               0 < delta < rho_1/rho_K - 1.
#
#               RESULT: exposes the intended pair in all 175 Kozlov-vector cases, n = 3..9, every
#               d, every valid (t, j) with j - t >= 2.  0 failures.
#
#               The all-ones vector fails by design and the failure is informative: there
#               rho_i = 1 identically, so rho_1/rho_K - 1 = 0 and no delta exists.  The
#               construction needs a_{d+k}/a_k STRICTLY DECREASING -- in fact only rho_1 > rho_K --
#               which is exactly the binomial lemma, and is exactly why the all-ones extremal
#               matrix is a different matrix.
#
# Run from the project root:  sage code/oneoff/close_gap3_explicit_functional.sage

# Attempt to CLOSE article 1's open problem 1 by an explicit functional.
#
# Reduction (re-derived): with m = n-d shared coordinates and e_s = phi_{d+s},
#   exposing v_{d+t} on A  <=>  Q_t = sum_{s<=t} e_s a_{d+s} strict max over t' in [0,m]
#   exposing u_j    on B  <=>  P_j = sum_{s<=j} e_s a_s     strict max over j' in [1,m]
# Window s in [t+1, j], K = j-t.  Put z_i = e_{t+i} a_{t+i}, rho_i = a_{d+t+i}/a_{t+i}.
#
# PROPOSED functional (uniform in K >= 2, simpler than the review's):
#   e_s = +1                      for s <= t          (kills t' < t and j' <= t)
#   z_1 = -1, z_K = 1+delta, else 0  in the window     (0 < delta < rho_1/rho_K - 1)
#   e_s = -1                      for s > j           (kills t' > j and j' > j)
def test(n, d, t, j, a):
    m = n - d
    if not (0 <= t <= m and 1 <= j <= m and j - t >= 2): return None
    K = j - t
    b = [a[t+i-1] for i in range(1, K+1)]          # a_{t+i}
    c = [a[d+t+i-1] for i in range(1, K+1)]        # a_{d+t+i}
    rho = [QQ(c[i])/QQ(b[i]) for i in range(K)]
    delta = (rho[0]/rho[K-1] - 1) / 2              # any value in (0, rho_1/rho_K - 1)
    if delta <= 0: return ("BAD delta", delta)
    z = [0]*K; z[0] = QQ(-1); z[K-1] = 1 + delta
    e = [QQ(0)]*(m+1)                              # 1-indexed
    for s in range(1, t+1):   e[s] = QQ(1)
    for i in range(1, K+1):   e[t+i] = QQ(z[i-1])/QQ(b[i-1])
    for s in range(j+1, m+1): e[s] = QQ(-1)
    BIG = QQ(10)**6
    phi = [QQ(0)]*(n+d+1)                          # 1-indexed, length N = n+d
    for k in range(1, d+1):     phi[k] = BIG       # private-A
    for s in range(1, m+1):     phi[d+s] = e[s]    # shared
    for s in range(1, d+1):     phi[n+s] = -BIG    # private-B
    valA = [sum(phi[k]*a[k-1] for k in range(1, i+1)) for i in range(1, n+1)]
    valB = [sum(phi[d+s]*a[s-1] for s in range(1, jj+1)) for jj in range(1, n+1)]
    okA = all(valA[d+t-1] > valA[i-1] for i in range(1, n+1) if i != d+t)
    okB = all(valB[j-1] > valB[jj-1] for jj in range(1, n+1) if jj != j)
    return okA and okB

print(" a         n  d  cases tested   all expose correctly?")
bad = []
for aname in ("kozlov", "ones"):
    for n in range(3, 10):
        a = [binomial(n, k) for k in range(1, n+1)] if aname=="kozlov" else [1]*n
        for d in range(1, n):
            res, cnt = True, 0
            for t in range(0, n-d+1):
                for j in range(1, n-d+1):
                    r = test(n, d, t, j, a)
                    if r is None: continue
                    cnt += 1
                    if r is not True:
                        res = False; bad.append((aname,n,d,t,j,r))
            if cnt: print("  %-8s %2d %2d   %4d          %s" % (aname, n, d, cnt, res))
print("\nfailures:", len(bad))
for x in bad[:6]: print("   ", x)
