#!/usr/bin/env python3
"""Independent finite diagnostics for the type A proof.

Usage: python3 check_type_a.py 6
       python3 check_type_a.py 7

Uses direct threshold rank matrices rather than the manuscript's prior
sorted-prefix implementation. Exhausts every (w, record pair, threshold,
maximal filtered element) in S_n. These checks are finite corroboration;
they are not an arbitrary-rank proof or a formal proof assistant certificate.
No external dependencies are required.
"""
from itertools import permutations
from functools import lru_cache
from collections import Counter
import time,json

def rank(p):
 n=len(p)
 return tuple(sum(v>=r for v in p[:k]) for k in range(1,n) for r in range(2,n+1))
def leq(p,q): return all(a<=b for a,b in zip(rank(p),rank(q)))
def swap(p,i,j):
 a=list(p);a[i],a[j]=a[j],a[i];return tuple(a)
def leng(p): return sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def records(w):
 out=[];cur=0
 for j,d in enumerate(w[1:],1):
  if cur<d<w[0]:out.append((j,d,swap(w,0,j)));cur=d
 return out

def main(n):
 start=time.time();ps=list(permutations(range(1,n+1)));index={p:i for i,p in enumerate(ps)};rs=[rank(p) for p in ps];ls=[leng(p) for p in ps]
 lower=[];upper=[0]*len(ps)
 for j,r in enumerate(rs):
  bits=0
  for i,s in enumerate(rs):
   if all(a<=b for a,b in zip(s,r)): bits|=1<<i;upper[i]|=1<<j
  lower.append(bits)
 print('built',n,time.time()-start,flush=True)
 def ids(bits):
  while bits:
   v=bits&-bits;bits-=v;yield v.bit_length()-1
 def B(x,c):
  return next((v for v in x[1:] if x[0]<v<=c),None)
 def roots(x,w):
  return [(x[i],x[j],i,j) for i in range(n) for j in range(i+1,n) if x[i]<x[j] and (lower[index[w]]>>index[swap(x,i,j)])&1]
 checks=Counter();failures=[]
 for wi,w in enumerate(ps):
  rec=records(w);c=w[0]
  for s,(js,a,zs) in enumerate(rec):
   for t in range(s+1,len(rec)):
    jt,d,zt=rec[t]
    common=lower[index[zs]]&lower[index[zt]]
    x0=list(w);x0[0]=a;x0[js]=d;x0[jt]=c;x0=tuple(x0)
    assert common==lower[index[x0]],('meet',w,s,t)
    filt=common
    for jh,dh,zh in rec[s+1:t]:filt&=~lower[index[zh]]
    for b in range(d+1,c+1):
     F=sum(1<<i for i in ids(filt) if B(ps[i],c)>=b)
     for xi in ids(F):
      if upper[xi]&F !=1<<xi: continue
      x=ps[xi];checks['maxima']+=1
      assert x[0]==a and B(x,c)==c,('normalization',w,s,t,b,x)
      rz=roots(x,zt);rw=roots(x,w)
      L={l for l,m,*_ in rz if m<c};M={m for l,m,*_ in rz if m<c};H={m for l,m,*_ in rz if l==c};p,q,h=len(L),len(M),len(H)
      actual={(l,m) for l,m,*_ in rz};expected={(l,m) for l in L for m in M}|{(c,hv) for hv in H}
      assert L and a in L and q and actual==expected,('lower roots',w,s,t,b,x,rz,expected)
      assert max(L)<=a and min(M)>a and max(M)<c and all(hv>c for hv in H),('lower sets',w,s,t,b,x,L,M,H)
      assert (h==0 and p>=2) or (h>0 and q==1),('parameters',w,s,t,b,x,p,q,h)
      assert ls[index[zt]]-ls[xi]==p+q+h-1,('lower dimension',w,s,t,b,x,p,q,h)
      expw=({(l,m) for l in L for m in M|{c}} if h==0 else {(l,m) for l in L for m in {d,c}}|{(m,hv) for m in {d,c} for hv in H})
      assert {(l,m) for l,m,*_ in rw}==expw,('ambient roots',w,s,t,b,x,rw,expw)
      assert ls[wi]-ls[xi]==p+q+h,('ambient dimension',w,s,t,b,x,p,q,h)
      # verify maximal singularity with type A tangent criterion
      sing=[vi for vi in ids(lower[wi]&upper[xi]) if len(roots(ps[vi],w))>ls[wi]-ls[vi]]
      assert sing==[xi],('not maximal sing',w,s,t,b,x,[ps[vi] for vi in sing])
      checks[(p,q,h)]+=1
 print('DONE',n,time.time()-start,dict((str(k),v) for k,v in checks.items()),flush=True)
 return checks
if __name__=='__main__':
 import sys
 main(int(sys.argv[1]) if len(sys.argv)>1 else 5)
