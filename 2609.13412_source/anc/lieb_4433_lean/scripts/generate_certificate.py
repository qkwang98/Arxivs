#!/usr/bin/env python3
"""Generate transparent Lean literals; kernel-checked theorems live elsewhere."""
from pathlib import Path
import json
from fractions import Fraction
root=Path(__file__).resolve().parents[1]
data=json.loads((root/'specification/exact_certificate/certificate.json').read_text())
def shape(a):return '['+', '.join(map(str,a))+']'
def rat(a):
 x=Fraction(a)
 return f'({x.numerator} : ℚ)' if x.denominator==1 else f'({x.numerator} / {x.denominator} : ℚ)'
def rowsparse(d):
 return '['+', '.join('('+shape(list(map(int,k.split(','))))+', '+rat(v)+')' for k,v in d.items())+']'
lines=['import Bridge.CertificateAlgorithm','','namespace LiebBridge.Certificate','']
for i,w in enumerate(data['rows'],1):
 lines += [f'def witness{i:02d} : Witness :=', '  { k := '+str(w['k']), '    eta := '+shape(w['eta']), '    mu := '+shape(w['mu']), '    sign := '+rat(w['sign']), '    weight := '+rat(w['weight']), '    coefficients := '+rowsparse(w['coefficients'])+' }','']
lines += ['def rows : List Witness :=','  ['+', '.join(f'witness{i:02d}' for i in range(1,21))+']','', 'def identityEntries : List (Shape × ℚ) :=','  '+rowsparse(data['identity']),'','def identityCoeff (nu : Shape) : ℚ := sparseCoeff identityEntries nu','','def weightedStoredCoeff (nu : Shape) : ℚ :=','  (rows.map fun w => w.weight * storedCoeff w nu).sum','','def weightedComputedCoeff (nu : Shape) : ℚ :=','  (rows.map fun w => w.weight * computedCoeff w nu).sum','','end LiebBridge.Certificate','']
(root/'Bridge/CertificateData.lean').write_text('\n'.join(lines))
