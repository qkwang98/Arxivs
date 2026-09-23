from core import partitions, dimension, horizontal_children, witness
from functools import lru_cache
import json, collections
from pathlib import Path
HERE=Path(__file__).resolve().parent

def kappa(lam):return sum(x*(x+1-2*i)//2 for i,x in enumerate(lam,1))
def max_corner(lam):return max(x-i for i,x in enumerate(lam,1) if i==len(lam) or x>lam[i])

def longrow(lam):
 if len(lam)<=1:return True
 rho=lam[1:]
 return lam[0]>=sum(rho)+max_corner(rho)-1

def old_seed(lam):
 n=sum(lam)
 if n<=15:return True
 large=tuple(x for x in lam if x>=3)
 if len(large)<=3 or (len(large)==4 and large[1]==large[2]):return True
 if len(lam)==4 and lam[1:]==(4,3,3):return True
 # retain exact input certificate for order17, separately tabulated
 if lam in [(6,5,3,3)]:return True
 return False

def new_seed(lam):
 if old_seed(lam) or longrow(lam):return True
 if len(lam)==4 and lam[2:]==(3,3) and 5*lam[0]>=8*lam[1]:return True
 return False

def move_children(lam):
 for i,x in enumerate(lam):
  if x>max(lam[i+1] if i+1<len(lam) else 0,1):
   v=list(lam);v[i]-=1;v.append(1);yield tuple(v)

def node_closure(n,seed):
 ps=partitions(n)
 good={lam for lam in ps if seed(lam)}
 todo=list(good)
 while todo:
  x=todo.pop()
  for y in move_children(x):
   if y not in good:good.add(y);todo.append(y)
 return good

def analytic_old(lam):
 if sum(lam)<=15:return True
 large=tuple(x for x in lam if x>=3)
 t=lam.count(1)
 if len(large)<=3:return True
 if len(large)==4:
  a,b,c,d=large
  if t>=b-c:return True
  if b==4 and c==d==3 and lam.count(2)==0:return True
 # isolated input 6533 closure, at order17 only
 if sum(lam)==17 and len(lam)-lam.count(1)<=4 and all(x<=y for x,y in zip(lam,(6,5,3,3))):return True
 return False

def analytic_new(lam):
 if analytic_old(lam):return True
 core=tuple(x for x in lam if x>=2)
 t=lam.count(1)
 if len(core)<=1:return True
 a=core[0];rho=core[1:]
 if a+t>=sum(rho)+max_corner(rho)-1:return True
 return len(core)==4 and core[2:]==(3,3) and 5*(a+t)>=8*core[1]

if __name__=='__main__':
 stats=[];residual={}
 for n in range(16,31):
  ps=partitions(n);old=node_closure(n,old_seed);new=node_closure(n,new_seed)
  assert all((l in old)==analytic_old(l) for l in ps)
  assert all((l in new)==analytic_new(l) for l in ps)
  rem=[l for l in ps if l not in new]
  by=collections.Counter(len([x for x in l if x>=3]) for l in rem)
  r={'n':n,'partitions':len(ps),'old_covered':len(old),'new_covered':len(new),'newly_covered':len(new-old),'residual':len(rem),'residual_4large':by[4],'residual_ge5large':sum(v for k,v in by.items() if k>=5)}
  print(r,flush=True);stats.append(r);residual[n]=rem
 json.dump(stats,open(HERE/'frontier_counts.json','w'),indent=2)
 json.dump(residual,open(HERE/'residual_shapes.json','w'),indent=2)
 # complete exact checks of long-row witness criterion and hereditary fact
 c=0
 for q in range(1,19):
  for rho in partitions(q):
   C=max_corner(rho);m=max(rho[0],q+C-1)
   rr=witness(m,rho,1)
   lam=(m,)+rho
   assert rr[lam]==-q
   assert all(x>=0 for nu,x in rr.items() if nu!=lam)
   for nu in rr:
    if nu!=lam:assert longrow(nu)
   if m>rho[0]:
    row=witness(m-1,rho,1)
    assert any(v<0 for nu,v in row.items() if nu!=(m-1,)+rho)
   c+=1
 print('long-row exact examples',c,flush=True)
