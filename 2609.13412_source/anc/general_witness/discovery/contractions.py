"""Exact central-Young partial-swap witnesses, using marked-cycle counting."""
from research import *
from itertools import permutations, product
from collections import defaultdict
@lru_cache(None)
def cycles(s):
    seen=set(); ans=[]
    for i in range(len(s)):
        if i in seen: continue
        c=[]; j=i
        while j not in seen:
            seen.add(j);c.append(j);j=s[j]
        ans.append(tuple(c))
    return tuple(ans)
@lru_cache(None)
def perms(k): return tuple(permutations(range(k)))
def canonical(rho):
    out=[];j=0
    for r in rho: out.extend(list(range(j+1,j+r))+[j]);j+=r
    return tuple(out)
@lru_cache(None)
def weak_compositions(n,k):
    if k==0: return ((),) if n==0 else ()
    if k==1:return ((n,),)
    return tuple((j,)+b for j in range(n+1) for b in weak_compositions(n-j,k-1))
@lru_cache(None)
def states(p,k):
    return tuple((a,r,factorial(p-k)//z(r))
           for m in range(p-k+1) for a in weak_compositions(m,k) for r in partitions(p-k-m))
def typed(cyc,a,tail):
    return tuple(sorted(tail+tuple(len(c)+sum(a[i] for i in c) for c in cyc),reverse=True))

def counts(p,q,k):
    file=ROOT/f'counts_{p}_{q}_{k}.pkl'
    if file.exists():return pickle.loads(file.read_bytes())
    pp=partitions(p);qq=partitions(q); nn=partitions(p+q)
    pi={a:i for i,a in enumerate(pp)}; qi={a:i for i,a in enumerate(qq)}; ni={a:i for i,a in enumerate(nn)}
    ans=np.zeros((len(pp),len(qq),len(nn)),dtype=object)
    A=states(p,k);B=states(q,k); raw=defaultdict(int)
    ts=[(t,cycles(t)) for t in perms(k)]
    start=time.time()
    for sr in partitions(k):
        s=canonical(sr); sc=cycles(s); multiplicity=factorial(k)//z(sr)
        ainfo=[(a,r,w*multiplicity,typed(sc,a,r)) for a,r,w in A]
        for t,tc in ts:
            cc=cycles(tuple(s[t[i]] for i in range(k)))
            tcc=tuple(tuple(t[i] for i in c) for c in cc)
            binfo=[(b,r,w,typed(tc,b,r),tuple(sum(b[i] for i in c) for c in cc)) for b,r,w in B]
            for a,r,w,rtype in ainfo:
                aa=tuple(2*len(c)+sum(a[j] for j in d) for c,d in zip(cc,tcc))
                for b,rr,ww,stype,bb in binfo:
                    ntype=tuple(sorted(r+rr+tuple(v+u for v,u in zip(aa,bb)),reverse=True))
                    raw[(rtype,stype,ntype)]+=w*ww
    for (r,s,t),v in raw.items(): ans[pi[r],qi[s],ni[t]]=v
    assert sum(ans.flat)==factorial(p)*factorial(q),(p,q,k,sum(ans.flat))
    for i,r in enumerate(pp):
        for j,s in enumerate(qq):
            assert sum(ans[i,j,:])==factorial(p)//z(r)*factorial(q)//z(s)
    file.write_bytes(pickle.dumps(ans))
    print('counts',p,q,k,'entries',len(raw),'time',round(time.time()-start,2),flush=True)
    return ans

def full_data(n):
    file=ROOT/f'full_swap_{n}.pkl'
    if file.exists(): return pickle.loads(file.read_bytes())
    d=data(n); ps=d['parts'];fs=np.array(d['dims'],dtype=object);Tn=table(n)
    rows=list(d['rows']);labels=[(a,b,1) for a,b in d['labels']]; rowset=set(rows)
    bylabel={label:row for label,row in zip(labels,rows)}
    zero=0; duplicate=0; allcount=len(rows)
    for p in range(2,n//2+1):
        q=n-p;P=partitions(p);Q=partitions(q);Tp=table(p);Tq=table(q)
        for k in range(2,p+1):
            C=counts(p,q,k)
            D=np.zeros((len(P),len(Q),len(ps)),dtype=object)
            for l in range(len(ps)):
                D[:,:,l]=Tp@C[:,:,l]@Tq.T
            D=D@Tn.T
            for i,a in enumerate(P):
                for j,b in enumerate(Q):
                    if p==q and j<i:continue
                    allcount+=1
                    row=D[i,j,:]
                    assert sum(row*fs)==0,(n,p,k,a,b)
                    if not any(row): zero+=1;continue
                    g=0
                    for v in row:g=gcd(g,abs(int(v)))
                    r=tuple(int(v)//g for v in row)
                    bylabel[(a,b,k)]=r
                    if r in rowset:duplicate+=1;continue
                    rowset.add(r);rows.append(r);labels.append((a,b,k))
            print('n',n,'p',p,'k',k,'unique rows',len(rows),flush=True)
    out={'n':n,'parts':ps,'dims':d['dims'],'rows':rows,'labels':labels,'bylabel':bylabel,
         'allcount':allcount,'zero':zero,'duplicates':duplicate}
    file.write_bytes(pickle.dumps(out));return out

if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:] or [14,15]):
        d=full_data(n)
        print('Generated',n,'distinct nonzero rays',len(set(d['rows'])))
