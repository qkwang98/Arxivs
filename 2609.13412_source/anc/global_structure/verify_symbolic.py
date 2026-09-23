"""Exact symbolic verification of the infinite (a,b,3,3) theorem.
Run `python verify_symbolic.py`. No third-party packages are needed.
"""
from polynomials import P, family_H, global_bernstein, bernstein_coefficients
from math import comb
import json
from pathlib import Path

def verify(build=False):
    g,u,x=[P.var(i) for i in range(3)]
    certificate=[];translated_count=0;point_count=0
    for c in range(4):
        b=g+u+(5 if c==3 else 3)
        a=8*b/5+(2*b/5+4)*x
        bs=global_bernstein(c)
        reconstructed=sum((bs[k]*comb(4,k)*x**k*(1-x)**(4-k) for k in range(5)),P(0))
        assert reconstructed==family_H(a,b,g,c)
        for k,Q in enumerate(bs):
            # Infinite quadrant g>=10,u>=10.
            R=Q.subst(0,g+10).subst(1,u+10)
            assert R.nonnegative_coefficients(),('quadrant',c,k)
            translated_count+=1
            # Twenty infinite strips.
            for i in range(10):
                R1=Q.subst(0,i).subst(1,u+10)
                R2=Q.subst(1,i).subst(0,g+10)
                assert R1.nonnegative_coefficients(),('strip g',c,k,i)
                assert R2.nonnegative_coefficients(),('strip u',c,k,i)
                translated_count+=2
            # Remaining finite grid, omitting b<4 and b=7.
            # The complete exceptional integer b=7 family is handled below.
            for i in range(10):
                for j in range(10):
                    bv=i+j+(5 if c==3 else 3)
                    if bv<4 or bv==7:continue
                    assert Q.value(i,j,0)>=0,('grid',c,k,i,j)
                    point_count+=1
            certificate.append({'c':c,'k':k,'terms':Q.to_json()})
    # Integer b=7: 5a>=8b implies a>=12, so use interval [12,18].
    exceptional=[]
    for c in range(4):
        for gv in range(5):
            if c==3 and gv==4:continue
            bs=bernstein_coefficients(family_H(12+6*x,7,gv,c))
            assert all(Q.nonnegative_coefficients() for Q in bs),('b7',c,gv)
            exceptional.append({'c':c,'g':gv,'bernstein':[str(Q.value(0,0,0)) for Q in bs]})
    # Two exact special-coordinate identities, in independent variables a,b.
    a,b=P.var(0),P.var(1)
    T=2*b*(b+1)*(b+8)*(a-b+2)
    assert family_H(a,b,b-3,3)==-T
    assert family_H(a,b,b-4,3)==0
    result={'domain':'integer b>=4, 5a>=8b; two-witness interval a<=2b+4',
            'variables':['g','u','x'],'grid_shift':10,
            'bernstein_polynomials':certificate,'b7_exception':exceptional}
    path=Path(__file__).with_name('symbolic_certificate.json')
    if build:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result
    print(f'PASS: 20 exact Bernstein polynomial identities; {translated_count} nonnegative shifted polynomials; {point_count} rational grid values.')
    print('PASS: all 19 exceptional b=7 off-target coordinates on the full interval [12,18].')
    print('PASS: target coefficient -2b(b+1)(b+8)(a-b+2); gap-one coordinate zero.')
    return result

if __name__=='__main__':
    import sys
    verify('--build' in sys.argv)
