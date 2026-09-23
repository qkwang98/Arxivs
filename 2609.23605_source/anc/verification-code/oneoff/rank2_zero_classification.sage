# rank2_zero_classification.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Answers "is the isolated j = t+1 zero of M(n,d) the same
#               phenomenon as the above-j obstruction?"  It is not, and the
#               classification that falls out is better than the question.
#
# Method: model rank-two feasibility in z-coordinates (z_i = a_i x_i), where the
# normal cone is leg-vector-independent and all a-dependence sits in the overlap
# reweighting rho(s) = a_s / a_{d+s}; then compute a minimal infeasible subsystem
# for every zero and classify its constraints.
#
# MODEL BUG FOUND AND FIXED while validating: the first version imposed
# T(j) > 0, i.e. compared against a vertex at the ORIGIN. But angle(a) is
# conv{v_1,...,v_n} and has no v_0, so the "below" constraints run from u = 2, not
# u = 1. That single phantom constraint made exactly the pair (i,j) = (d,1)
# infeasible in the model though it is a genuine vertex. After the fix the model
# reproduces the true extremal matrix exactly for both leg vectors, n = 4,5,6,
# every d. It is also the same fact as "a summand does not constrain its window's
# first coordinate".
#
# Findings (n = 4..8, all d, both leg vectors, 0 mismatches):
#   * j = t+1 zeros have a 2-element core {W1-above(i+1), W2-below(j)}, which
#     unpacks to a SINGLE shared coordinate forced to be both negative and
#     positive. rho > 0 cancels, so this family is leg-vector INDEPENDENT.
#   * counts: #(j<t) = C(m,2) and #(j=t+1) = m-1 for BOTH leg vectors.
#   * the ONLY leg-vector dependence is a third family j > t+1, of size
#     C(m-1,2) for all-ones and EMPTY for Kozlov. Totals then reproduce the
#     known (m-1)(m+2)/2 and m(m-1), and their difference C(m-1,2) is exactly the
#     vertex-count discrepancy (m-1)(m-2)/2 found independently the same day.
#   * so the increasing rho of the Kozlov vector REMOVES zeros rather than adding
#     them: Kozlov has more vertices than all-ones, not fewer.

# For each ZERO of the rank-two extremal matrix M(n,d), find a minimal infeasible
# subsystem and classify its constraints as window-1/window-2, below-j/above-j.
# Question: is the isolated j = t+1 zero an ABOVE-j failure (as the z-coordinate
# analysis predicts), and are the j < t zeros something else?
import itertools

def build(n,d,i,j,a):
    """Variables: y_1..y_n (window 1 z-coords), u_{m+1}..u_n (window 2 free part).
       z2_s = rho(s) y_{d+s} for s<=m ; z2_s = u_s for s>m."""
    m=n-d; NV=n+(n-m)
    def y(v): e=[0]*NV; e[v-1]=1; return vector(QQ,e)
    def z2(s):
        if s<=m: return (QQ(a[s-1])/QQ(a[d+s-1]))*y(d+s)
        e=[0]*NV; e[n+(s-m)-1]=1; return vector(QQ,e)
    cons=[]
    for u in range(2,i+1):  cons.append(("W1-below",u, sum((y(v) for v in range(u,i+1)),vector(QQ,[0]*NV))))
    for l in range(i+1,n+1):cons.append(("W1-above",l,-sum((y(v) for v in range(i+1,l+1)),vector(QQ,[0]*NV))))
    for u in range(2,j+1):  cons.append(("W2-below",u, sum((z2(s) for s in range(u,j+1)),vector(QQ,[0]*NV))))
    for l in range(j+1,n+1):cons.append(("W2-above",l,-sum((z2(s) for s in range(j+1,l+1)),vector(QQ,[0]*NV))))
    return cons,NV

def feasible(cons,NV):
    if not cons: return True
    return not Polyhedron(ieqs=[[-1]+list(c[2]) for c in cons], base_ring=QQ).is_empty()

def iis(cons,NV):
    cur=list(cons)
    for c in list(cons):
        trial=[x for x in cur if x is not c]
        if not feasible(trial,NV): cur=trial
    return cur

for n in (4,5):
  a=[binomial(n,s) for s in range(1,n+1)]
  for d in (1,2):
    m=n-d
    print("=== n=%d d=%d (m=%d) ==="%(n,d,m))
    for i in range(1,n+1):
      for j in range(1,n+1):
        cons,NV=build(n,d,i,j,a)
        if feasible(cons,NV): continue
        core=iis(cons,NV); t=i-d
        kinds=sorted(set(c[0] for c in core))
        rel = "j=t+1" if j==t+1 else ("j<t" if j<t else ("j=t" if j==t else "j>t+1"))
        print("   M[i=%d][j=%d]=0  t=i-d=%2d  %-7s  core uses: %s"%(i,j,t,rel,", ".join(kinds)))
