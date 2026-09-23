"""Refine the common contour radius and formal order of the parameter series."""
import argparse
import hashlib
import json
from pathlib import Path

from mpmath import mp

import anchored_psi as ap
import high_precision as hp
import pii_core as pii
from compare_pii import encode
from parameter_study import CASES, metrics, weighted_difference


def decode(raw):
    return mp.matrix([[mp.mpc(*v) if isinstance(v,list) else mp.mpf(v) for v in row] for row in raw])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--cases', nargs='+', choices=CASES, default=list(CASES))
    args = parser.parse_args()
    mp.dps = 70
    for name in args.cases:
        kind,a,b = CASES[name]
        source = args.input/name/'results.json'
        data = json.loads(source.read_text())
        if data['status'] != 'complete':
            raise ValueError('Unresolved main experiment: '+name)
        output = source.with_name('truncation_check.json')
        if output.exists():
            raise FileExistsError(output)
        print(name+': radius and formal-order refinement', flush=True)
        if kind == 'PII':
            ref = pii.Reference(u0=a, w0=b)
            contour = pii.Contours(ref, radius=4.5, formal_order=64, tolerance='1e-12')
            settings = {'radius':4.5, 'formal_order':64, 'tolerance':'1e-12'}
        else:
            p = hp.Parameters()
            p.a = mp.mpc(a,b)
            ref = hp.TaylorReference(6,70,'1e-36',40,parameters=p)
            contour = ap.AnchoredContours(ref, radius=15, formal_order=48, tolerance='1e-29')
            settings = {'radius':15, 'formal_order':48, 'tolerance':'1e-29'}
        jac = {t:decode(data['monitors'][1]['J'][str(t)]) for t in data['points']}
        old = {t:decode(data['contours'][2]['F'][str(t)]) for t in data['points']}
        values = {t:(contour.at(t)[0] if kind == 'PII' else contour.at(t)) for t in data['points']}
        result = {'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                  'settings':settings, 'F':values,
                  'increment':weighted_difference(values,old,jac),
                  **metrics(values,{t:ref.matrix(t) for t in values},jac)}
        output.write_text(json.dumps(encode(result),indent=2)+'\n')
        print('  weighted increment '+mp.nstr(result['increment'],6),flush=True)


if __name__ == '__main__':
    main()
