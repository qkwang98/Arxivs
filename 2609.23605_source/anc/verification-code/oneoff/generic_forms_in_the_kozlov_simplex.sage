# generic_forms_in_the_kozlov_simplex.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Locates the generic-form Hilbert functions of
#               Snellman--Moreno-Socias inside the Kozlov simplex.
#
# Prompted by Jan's remark that in arXiv:math/0007089 (Homology, Homotopy and
# Applications 4(2), 2002, 409-426) the Hilbert series of E/(f), f a generic form
# of odd degree d, was understood by multiplying by 1 + t^d.  That factor has an
# exact-sequence behind it: f odd forces f^2 = 0, so (E, .f) is a complex, and
# genericity makes it as exact as possible, whence
#     HS(E/(f)) * (1 + t^d) = (1+t)^n
# up to the truncation at the first non-positive coefficient.
#
# General fact this script exhibits, valid for ANY point of Koz(n), not just the
# generic ones: the barycentric coordinates with respect to the Kozlov vertices
# v_1,...,v_n are the successive differences of the LYM ratios,
#     lambda_j = mu_j - mu_{j+1},     mu_j = h_j / C(n,j).
# So lying in Koz(n) is equivalent to mu being weakly decreasing from mu_1 = 1 --
# which is exactly local LYM.  This is the geometric content of Lemma lem-mu.
#
# Findings: the generic points are BOUNDARY points, on the face spanned by those
# v_j where mu strictly drops; the face dimension grows roughly with n/d.  For
# d = n with n odd the generic point is exactly the VERTEX v_{n-1}.
# Cross-check: n = 7, d = 3 reproduces (7,21,34,28,0,0,0), the value verified in
# Macaulay2 over Z/31991 on 2026-08-02 (see LOGBOOK-session-07).

# Where does the GENERIC-form Hilbert function sit inside the Kozlov simplex?
# Moreno-Socias-Snellman: HS(E/(f)) = ceil( (1+t)^n / (1+t^d) ), truncated at the
# first non-positive coefficient.  The (1+t^d) factor is exactly Jan's remark.
R.<t> = PowerSeriesRing(QQ, default_prec=40)
def generic_hs(n,d):
    s = ((1+t)^n / (1+t^d)).list()
    out=[]
    for c in s[:n+1]:
        if c<=0: break
        out.append(ZZ(c))
    return out                       # [c_0, c_1, ..., ] truncated

print("Barycentric coordinates of the generic point w.r.t. the Kozlov vertices v_1..v_n.")
print("Claim: lambda_j = mu_j - mu_{j+1}, mu_j = h_j / C(n,j) -- the LYM ratios of lem-mu.")
print("So the point lies in the face spanned by the v_j where mu strictly drops.\n")
print("  n  d   h = (h_1..h_n)                       mu strictly drops at    face dim")
for n in (5,6,7,8,9):
  for d in (3,5,7):
    if d>n: continue
    hs=generic_hs(n,d)
    h=[hs[j] if j<len(hs) else 0 for j in range(1,n+1)]
    mu=[QQ(h[j-1])/binomial(n,j) for j in range(1,n+1)]+[0]
    lam=[mu[j]-mu[j+1] for j in range(n)]
    supp=[j+1 for j in range(n) if lam[j]>0]
    assert sum(lam)==1 and all(l>=0 for l in lam), (n,d,lam)
    # verify it really is the barycentric combination
    c=[binomial(n,i) for i in range(1,n+1)]
    V=[vector(QQ,c[:j]+[0]*(n-j)) for j in range(1,n+1)]
    assert sum(lam[j]*V[j] for j in range(n))==vector(QQ,h)
    print("  %d  %d   %-36s %-22s %d" % (n,d,tuple(h),supp,len(supp)-1))
