#!/usr/bin/env python3
"""Independent S_n diagnostics for the horizontal-component argument.

Usage: python3 check_type_a_auxiliary.py 6

Checks the claimed horizontal-incidence formula using independent bipartite
perfect matching, then checks every applicable greedy step and the complete
horizontal-to-prefix construction. The tests verify only the finite rank
specified on the command line; the general proofs are in Section 3.
"""
from itertools import permutations
from collections import Counter
import time,json

def swap(p,i,j):
 q=list(p);q[i],q[j]=q[j],q[i];return tuple(q)
def rk(p):
 return tuple(sum(v>=r for v in p[:k]) for k in range(1,len(p)) for r in range(2,len(p)+1))
def perfect_matching(I,J,b,c):
 # Independent augmenting-path matching in the upper-triangular support,
 # with one prescribed matrix entry deleted.
 assigned={}
 def augment(row,seen):
  for col in J:
   if row>col or (row,col)==(b,c) or col in seen:continue
   seen.add(col)
   if col not in assigned or augment(assigned[col],seen):
    assigned[col]=row;return True
  return False
 return all(augment(row,set()) for row in I)
def main(n):
 ps=list(permutations(range(1,n+1)));idx={p:i for i,p in enumerate(ps)}
 ranks=list(map(rk,ps));le=[[all(a<=b for a,b in zip(r,s)) for s in ranks] for r in ranks]
 def B(p,c):return next(v for v in p[1:] if p[0]<v<=c)
 def targets(p,wi):return [p[j] for j in range(1,n) if p[0]<p[j] and le[idx[swap(p,0,j)]][wi]]
 counts=Counter();start=time.time()
 for wi,w in enumerate(ps):
  c=w[0]
  rec=[];m=0
  for h,d in enumerate(w[1:],1):
   if m<d<c:rec.append((h,d,swap(w,0,h)));m=d
  for vi,v in enumerate(ps):
   if not le[vi][wi]:continue
   for b in range(1,c):
    jb=v.index(b)+1;Lb=next(k for k in range(2,n+1) if b<=w[k-1]<c)
    predicted=all(sum(t>c for t in v[:k])<sum(t>c for t in w[:k]) for k in range(jb,Lb))
    actual=all(perfect_matching(v[:k],w[:k],b,c) for k in range(1,n+1))
    assert actual==predicted,('Hall',w,v,b,actual,predicted)
    counts['horizontal_incidence_instances']+=1
   if v[0]>=c:continue
   b=B(v,c);targ=targets(v,wi)
   if len(targ)>=2 and b<c:
    j=v.index(b);k=next(h for h in range(j+1,n) if b<v[h]<=c);y=swap(v,j,k)
    assert le[vi][idx[y]] and le[idx[y]][wi] and y[0]==v[0] and B(y,c)>b and len(targets(y,wi))>=2,('greedy',v,w,y,targ,targets(y,wi))
    counts['greedy_lifts']+=1
   if b==c:continue
   jb=v.index(b)+1;Lb=next(k for k in range(2,n+1) if b<=w[k-1]<c)
   horizontal=all(sum(t>c for t in v[:k])<sum(t>c for t in w[:k]) for k in range(jb,Lb))
   active=[(h,d,z) for h,d,z in rec if d<b and le[vi][idx[z]]]
   if horizontal and active:
    hh,d,z=active[-1];x=v
    while x[0]<d:
     k=next(k for k in range(1,n) if x[0]<x[k]<=d);y=swap(x,0,k)
     assert le[idx[x]][idx[y]] and le[idx[y]][idx[z]] and B(y,c)==b
     x=y
    ax=[zz for h,dd,zz in rec if dd<b and le[idx[x]][idx[zz]]]
    assert ax==[z] and len(targets(x,wi))>=2,('two components',v,w,x,z,ax)
    # Raise B to c, then verify the promised prefix witness combinatorially.
    while B(x,c)<c:
     bb=B(x,c);j=x.index(bb);k=next(h for h in range(j+1,n) if bb<x[h]<=c);x=swap(x,j,k)
    ax=[(dd,zz) for h,dd,zz in rec if le[idx[x]][idx[zz]]]
    assert [zz for dd,zz in ax if dd<b]==[z] and any(dd>=b for dd,zz in ax) and len(targets(x,wi))>=2,('prefix witness',v,w,x,z,ax)
    counts['horizontal_prefix_witnesses']+=1
 print(json.dumps({'n':n,'seconds':time.time()-start,**counts},sort_keys=True))
if __name__=='__main__':
 import sys
 main(int(sys.argv[1]) if len(sys.argv)>1 else 6)
