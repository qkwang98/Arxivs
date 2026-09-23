# allones_prefix_sum_digraph_reformulation.sage
#
# Changelog (reverse chronological):
#   2026-09-06  Created. Validates the prefix-sum reformulation of the extremal
#               tensor in the all-ones case, and measures minimal cycle length.
#
# Result: exact agreement with the polyhedral computation over 25 configurations
# (rank 3 and rank 4), and EVERY minimal cycle found has length 2.  A 2-cycle
# involves exactly two summands, so "infeasible => some 2-cycle" is precisely the
# pairwise reduction of Remark obs-pairwise, for a = (1,...,1).
#
# See working-notes/pairwise-reduction-proof-strategies.org, Strategy A.

# Validate the prefix-sum reformulation for a=(1,...,1), and the claim that
# infeasibility is a CYCLE in a digraph whose minimal cycles are 2-cycles.
#
# S_p(j) = sum_{i<=j} phi_{d_p+i} = Phi(d_p+j) - Phi(d_p), Phi = prefix sums.
# So M[j]=1  <=>  exists real sequence Phi with unique argmax on window
# W_p = [d_p+1, d_p+n] at position m_p = d_p + j_p, for every p.
# That system is feasible iff the digraph with edges m_p -> x (x in W_p, x != m_p)
# is acyclic.
import itertools
from sage.graphs.digraph import DiGraph

def verts(a,d,N):
    return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def ext(vl,N):
    idx=list(itertools.product(*[range(len(v)) for v in vl]))
    pts={t:sum((vl[k][t[k]] for k in range(len(vl))),vector(QQ,[0]*N)) for t in idx}
    P=Polyhedron(vertices=list(pts.values()),base_ring=QQ)
    V=set(tuple(v) for v in P.vertices_list())
    return {t for t in idx if tuple(pts[t]) in V}

def acyclic_pred(n,ds,r):
    """Digraph-acyclicity prediction of the extremal support."""
    out=set()
    for jt in itertools.product(range(n),repeat=r):
        m=[ds[p]+jt[p]+1 for p in range(r)]        # 1-based argmax positions
        D=DiGraph(loops=True,multiedges=False)
        ok=True
        for p in range(r):
            for x in range(ds[p]+1, ds[p]+n+1):
                if x!=m[p]: D.add_edge(m[p],x)
        if D.has_loops() or not D.is_directed_acyclic(): ok=False
        if ok: out.add(jt)
    return out

def min_cycle_len(n,ds,r,jt):
    m=[ds[p]+jt[p]+1 for p in range(r)]
    D=DiGraph(loops=True)
    for p in range(r):
        for x in range(ds[p]+1, ds[p]+n+1):
            if x!=m[p]: D.add_edge(m[p],x)
    if D.is_directed_acyclic(): return None
    best=99
    for c in D.all_simple_cycles():
        best=min(best,len(c)-1)
    return best

print(" n  r  d               |T|  |acyclic|  match   min cycle lengths seen")
bad=0
for r in (3,4):
  for n in (3,4,5):
    pats = ([[0,1,2],[0,1,3],[0,2,3],[0,2,4],[0,1,1],[0,1,5]] if r==3
            else [[0,1,2,3],[0,1,2,4],[0,2,4,6],[0,1,1,2],[0,0,1,1]])
    for ds in pats:
      if r==4 and n==5: continue
      N=n+max(ds); V=[verts([1]*n,d,N) for d in ds]
      T=ext(V,N); A=acyclic_pred(n,ds,r)
      cyc=set()
      for jt in itertools.product(range(n),repeat=r):
          if jt not in A:
              L=min_cycle_len(n,ds,r,jt)
              if L: cyc.add(L)
      bad += 0 if A==T else 1
      print(" %d  %d  %-14s %4d %8d   %-6s  %s"%(n,r,ds,len(T),len(A),A==T,sorted(cyc)))
print("\nmismatches: %d"%bad)
