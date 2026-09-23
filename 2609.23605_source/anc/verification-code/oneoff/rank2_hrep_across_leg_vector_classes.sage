import itertools
def verts(a,d,N): return [vector(QQ,[0]*d+[a[j] for j in range(k)]+[0]*(N-d-k)) for k in range(1,len(a)+1)]
def R2(a,d,N):
    V1,V2=verts(a,0,N),verts(a,d,N)
    return Polyhedron(vertices=[V1[i]+V2[j] for i in range(len(a)) for j in range(len(a))],base_ring=QQ)
def hrep_ok(a,d):
    n=len(a); N=n+d; R=R2(a,d,N); C=[]
    for sh in (0,d):
        for j in range(1,n):
            u=vector(QQ,[0]*N); u[sh+j-1]=-QQ(1)/a[j-1]; u[sh+j]=QQ(1)/a[j]; C.append(u)
    u=vector(QQ,[0]*N); u[d]=-1; C.append(u)
    if n+1<=N: u=vector(QQ,[0]*N); u[n]=1; C.append(u)
    u=vector(QQ,[0]*N); u[N-1]=-1; C.append(u)
    eqs=[[h.b()]+list(h.A()) for h in R.Hrepresentation() if h.is_equation()]
    ieqs=[[max(u.dot_product(v.vector()) for v in R.vertices())]+list(-u) for u in C]
    Q=Polyhedron(ieqs=ieqs,eqns=eqs,base_ring=QQ)
    nf=len([h for h in R.Hrepresentation() if h.is_inequality()])
    return Q==R, nf, 2*n
print("Does the rank-2 H-description of conj-kozlov-hrep2 hold for other leg vectors?")
print("  a-class          n  d   Q == R ?   facets(R)   2n")
for label,mk in (("Kozlov (lc)",lambda n:[binomial(n,j) for j in range(1,n+1)]),
                 ("tent (lc)",  lambda n:[i*(n+1-i) for i in range(1,n+1)]),
                 ("2^i(n-i) (lc)",lambda n:[2^(i*(n-i)) for i in range(1,n+1)]),
                 ("all-ones",   lambda n:[1]*n),
                 ("factorial (lx)",lambda n:[factorial(i) for i in range(1,n+1)])):
  for n in (4,5):
    for d in (1,2):
      ok,nf,tn=hrep_ok(mk(n),d)
      print("  %-16s %d  %d   %-10s %7d %6d%s"%(label,n,d,ok,nf,tn," <-- facets != 2n" if nf!=tn else ""))
