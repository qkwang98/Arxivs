# zcoordinates_and_abel.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Verifies the z-coordinate reformulation of the rank-r
#               V-description obstruction, and which half of it Abel summation
#               dissolves. See working-notes/rank-r-vdescription-special-cases.org.
#
# Substituting z_i = a_i x_i turns the normal cone into
#   K(j) = { z : suffix sums ending at j positive, prefix sums after j negative }
# which does NOT mention the leg vector.  All a-dependence moves into the overlap
# map between consecutive windows, z^{(p+1)}_i = rho(i) z^{(p)}_{g+i} with
# rho(i) = a_i / a_{g+i}.  For all-ones rho == 1, which is the real reason that
# case is easy; for Kozlov rho is strictly increasing.
#
# Results:
#   1. Exact identity (n-i)(g+i+1) - (i+1)(n-g-i) = g(n+1), so rho(i+1)/rho(i) > 1
#      strictly for g >= 1.  Symbolic, not sampled.
#   2. Abel: rho increasing + suffix sums positive => reweighted suffix sums
#      positive.  59979 qualifying random samples, 0 violations.  So the "below j"
#      half of the gluing obstruction is free for the Kozlov vector.
#   3. The "above j" half is NOT preserved: 6321 counterexamples in 200000 trials.
#      Smallest witness w=(1,-3,-8,9), rho=(5,13,22,33), j=1, l=4: unweighted
#      prefix sums -3, -11, -2 all negative, reweighted 13(-3)+22(-8)+33(9) = +82.
#
# So the entire remaining content of the conjecture is the above-j half.

# z-coordinates: z_i = a_i * x_i.  Then the normal cone becomes
#   K(j) = { z : sum_{i=m}^{j} z_i > 0 for m <= j ;  sum_{i=j+1}^{l} z_i < 0 for l > j }
# which is INDEPENDENT of a.  All a-dependence moves into the reweighting between
# consecutive windows:  z^{(p+1)}_i = rho(i) * z^{(p)}_{g+i},  rho(i) = a_i / a_{g+i}.
var('n i g')
print("1) rho is strictly increasing for the Kozlov vector: the exact identity")
lhs = (n-i)*(g+i+1) - (i+1)*(n-g-i)
print("   (n-i)(g+i+1) - (i+1)(n-g-i)  simplifies to:", lhs.expand().factor())
print("   so rho(i+1)/rho(i) > 1 strictly whenever g >= 1.\n")

import itertools, random
def K_member(z,j):
    n=len(z)
    for m in range(1,j+1):
        if sum(z[m-1:j])<=0: return False
    for l in range(j+1,n+1):
        if sum(z[j:l])>=0: return False
    return True

print("2) Abel lemma: rho increasing positive + suffix sums positive => weighted suffix sums positive")
random.seed(int(11)); bad=0; tested=0
for trial in range(int(200000)):
    k=random.randint(int(2),int(6)); j=random.randint(1,k)
    w=[QQ(random.randint(-9,9)) for _ in range(k)]
    if any(sum(w[m-1:j])<=0 for m in range(1,j+1)): continue
    rho=sorted([QQ(random.randint(int(1),int(40))) for _ in range(k)])
    if len(set(rho))<k: continue
    tested+=1
    if any(sum(rho[m-1+e]*w[m-1+e] for e in range(j-m+1))<=0 for m in range(1,j+1)): bad+=1
print("   %d qualifying samples, %d violations  (0 expected)\n"%(tested,bad))

print("3) the OTHER half is NOT preserved: prefix sums negative, weighted prefix sum positive")
random.seed(int(12)); found=None; cnt=0
for trial in range(int(200000)):
    k=random.randint(int(2),int(5)); j=random.randint(0,k-1)
    w=[QQ(random.randint(-9,9)) for _ in range(k)]
    if any(sum(w[j:l])>=0 for l in range(j+1,k+1)): continue
    rho=sorted([QQ(random.randint(int(1),int(40))) for _ in range(k)])
    if len(set(rho))<k: continue
    for l in range(j+1,k+1):
        if sum(rho[t]*w[t] for t in range(j,l))>=0:
            cnt+=1
            if found is None: found=(w,rho,j,l)
            break
print("   counterexamples found: %d"%cnt)
if found: print("   smallest witness: w=%s rho=%s j=%s l=%s"%found)
