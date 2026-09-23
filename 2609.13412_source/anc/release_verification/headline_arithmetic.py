"""Independent standard-library arithmetic sanity checks, not an analytic proof."""
from math import factorial,prod
from fractions import Fraction
import json
from pathlib import Path

def dimension(lam):
    hooks=[lam[i]-j+sum(row>j for row in lam[i+1:]) for i in range(len(lam)) for j in range(lam[i])]
    return factorial(sum(lam))//prod(hooks)
def partition_number(n):
    counts=[1]+[0]*n
    for part in range(1,n+1):
        for total in range(part,n+1):counts[total]+=counts[total-part]
    return counts[n]
shapes=[(4,4,3,3),(6,5,3),(6,4,4),(5,5,4),(5,3,3,3)]
dims=[dimension(lam) for lam in shapes]
assert dims==[12012,15015,9009,6006,15015]
assert dimension((3,)*5)==6006
assert [partition_number(n) for n in [14,15]]==[135,176]
raw=[4035,6725,39759,23636]
weights=[Fraction(a*d,59512*dims[0]) for a,d in zip(raw,dims[1:])]
expected=[Fraction(x,238048) for x in [20175,20175,79518,118180]]
assert weights==expected and all(w>0 for w in weights) and sum(weights)==1
assert 59512*dims[0]==sum(a*d for a,d in zip(raw,dims[1:]))==714858144
assert sum(map(Fraction,['14/33','791/1485','2/55','2/297']))==1
assert [dimension(lam) for lam in [(5,4,4,1,1),(4,4,4,2,1),(4,4,4,1,1,1)]]==[100100,75075,50050]
assert 4*3726-3*4911-2501==-2330
result={'status':'PASS','order14_dimensions':dict(zip(map(str,shapes),dims)),'rectangle_dimension':6006,'p14':135,'p15':176,'normalized_bridge_weights':[str(w) for w in weights],'common_denominator_form':{'numerators':[20175,20175,79518,118180],'denominator':238048},'weight_sum':str(sum(weights)),'degree_balance':714858144,'order15_bridge_weight_sum':1,'term120_separator_pairing':-2330}
print(json.dumps(result,indent=2))
