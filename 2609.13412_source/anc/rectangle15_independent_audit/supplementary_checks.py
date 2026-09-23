#!/usr/bin/env python3
"""Independent bridge and small-degree trace checks; imports only our audit.py."""
from audit import *
from math import comb


def raw_content(p,beta,k,ps):
    row=[]
    for nu in ps:
        if not boxes(beta)<=boxes(nu): row.append(0); continue
        added=boxes(nu)-boxes(beta)
        if len({j for i,j in added})!=p: row.append(0); continue
        def P(x): return prod(x+j-i for i,j in added)
        r=p-k
        v=sum((-1)**(r-j)*comb(r,j)*P(j-p+1) for j in range(r+1))
        assert v%factorial(r)==0
        row.append(v//factorial(r))
    return row


def in_pate_class(nu):
    large=tuple(x for x in nu if x>=3)
    return len(large)<=3 or (len(large)==4 and large[1]==large[2])


def main():
    ps=parts(15)
    terms=[(1,(7,4,3),1,80),(5,(4,3,3),1,240),
           (3,(4,4,4),3,3),(4,(5,3,3),3,10),
           (4,(4,4,3),3,3),(4,(4,4,3),4,3),(6,(3,3,3),2,30)]
    rows=[raw_content(p,b,k,ps) for p,b,k,w in terms]
    # Recheck every bridge vector by the defining character sum, not solely
    # by the content formula. For a symmetric first block the exact factor is
    # F = k! (p-k)! (q-k)! N, with no primitive rescaling ambiguity.
    for (p,beta,k,w),row in zip(terms,rows):
        q=sum(beta)
        counts=concrete_counts(p,q,k)
        h=defaultdict(int)
        for (r,s,t),count in counts.items(): h[t]+=count*chi(beta,s)
        factor=factorial(k)*factorial(p-k)*factorial(q-k)
        direct=[sum(v*chi(nu,t) for t,v in h.items()) for nu in ps]
        assert direct==[factor*x for x in row]
        cycle_type.cache_clear(); concrete_extensions.cache_clear()
    total=[sum(t[3]*row[j] for t,row in zip(terms,rows)) for j in range(len(ps))]
    expected={(9,3,3):20*495,(8,4,3):20*226,(7,5,3):20*12,
              (7,4,4):20*4,(5,4,3,3):-20*198}
    assert total==[expected.get(nu,0) for nu in ps]
    target=(5,4,3,3)
    normalized={str(nu):str(Fraction(coef*f(nu),20*198*f(target))) for nu,coef in expected.items() if nu!=target}
    assert sum(Fraction(c*f(nu),20*198*f(target)) for nu,c in expected.items() if nu!=target)==1
    exceptions={str(n):[list(nu) for nu in parts(n) if not in_pate_class(nu)] for n in range(1,16)}
    assert all(not exceptions[str(n)] for n in range(1,14))
    assert exceptions['14']==[[4,4,3,3]]
    assert exceptions['15']==[[5,4,3,3],[4,4,3,3,1],[3,3,3,3,3]]

    # Completely direct group-algebra expansion of Tr(s e_beta e_gamma).
    # This is independent of the content rule used for the claimed trace.
    cases=0
    degree_counts={}
    for n in range(2,7):
        count=0
        for beta in parts(n-1):
            for gamma in parts(n-2):
                if not boxes(gamma)<boxes(beta): continue
                rem=next(iter(boxes(beta)-boxes(gamma))); c=rem[1]-rem[0]
                coefficients=defaultdict(int)
                for a in permutations(range(n-1)):
                    ca=chi(beta,cycle_type(a))
                    if not ca: continue
                    for b in permutations(range(n-2)):
                        cb=chi(gamma,cycle_type(b))
                        if not cb: continue
                        ae=a+(n-1,); be=b+(n-2,n-1)
                        ab=[ae[be[i]] for i in range(n)]
                        # s applied after a*b.
                        perm=tuple(n-1 if x==n-2 else n-2 if x==n-1 else x for x in ab)
                        coefficients[cycle_type(perm)]+=ca*cb
                factor=Fraction(f(beta)*f(gamma),factorial(n-1)*factorial(n-2))
                for nu in parts(n):
                    direct=factor*sum(coef*chi(nu,rho) for rho,coef in coefficients.items())
                    theoretical=Fraction(0)
                    if nu in children(beta):
                        add=next(iter(boxes(nu)-boxes(beta))); diff=add[1]-add[0]-c
                        assert diff!=0
                        theoretical=Fraction(f(gamma),diff)
                    assert direct==theoretical,(n,beta,gamma,nu,direct,theoretical)
                    count+=1
        cases+=count;degree_counts[n]=count
    result={'status':'PASS','bridge_coordinates_checked':len(ps),'bridge_rows_rechecked_by_defining_character_sum':7,
            'bridge_normalized_weights':normalized,'Pate_class_exceptions_through_15':exceptions,
            'branch_direct_trace_comparisons':cases,'trace_comparisons_by_order':degree_counts}
    Path(__file__).with_name('supplementary_results.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__': main()
