#!/usr/bin/env python3
"""Validate finite-lambda normalization against an independent spectral monitor."""
import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter

from mpmath import mp

import anchored_psi as a
from run_stabilized import encode, relative


def decode(raw):
    return mp.matrix([[mp.mpc(*v) for v in row] for row in raw])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'results/anchored_long')
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    source = Path(__file__).parent/'results/stabilized_long/results.json'
    baseline = json.loads(source.read_text())
    mp.dps = 90
    start = perf_counter()
    protected = [a.hp.c.ROOT/'piv2026_manuscript.tex',a.hp.c.ROOT/'ms_source.zip',
                 a.hp.c.ROOT/'ms_submission.zip',*sorted((a.hp.c.ROOT/'verification').glob('*'))]
    hashes = {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in protected if p.is_file()}
    print('Reference and finite-lambda transports',flush=True)
    ref = a.hp.TaylorReference(6,70,'1e-36',40)
    anchors = {name:a.AnchorTransport(ref,mp.mpf('1.45')*(1 if name == 'A' else -1)) for name in ('A','B')}
    saved = baseline['runs']['dps80_R18_N56']['values']
    j0 = decode(saved['0.0']['J'])
    data = {'reference':{k:v for k,v in baseline['reference'].items() if k != 'values'},
            'runs':{},'baseline_comparisons':baseline['comparisons'],
            'saved_monitor_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'protected_hashes':hashes}
    def checkpoint():
        (args.output/'results.json').write_text(json.dumps(data,indent=2)+'\n')
    tables = {}
    for digits,radius,order,tol,points in (
            (70,14,40,'1e-26',[-6.,.62,6.]),
            (80,18,56,'1e-36',[-6.,-3.,0.,.62,3.,6.])):
        name = f'dps{digits}_R{radius}_N{order}'
        print('Anchored run',name,flush=True)
        timing = perf_counter()
        with mp.workdps(digits):
            contours = a.AnchoredContours(ref,radius,order,tol,anchors)
            records,values = [],{}
            for t in points:
                print(f'  t={t:g}',flush=True)
                f = contours.at(t)
                ff = ref.matrix(t)
                jac = decode(saved[str(t)]['J'])
                record = {'t':t,'solution_error':relative(f,ff),
                          'variation_drift':relative(jac*f,j0),
                          'wronskian_error':float(abs(mp.det(f)-1)),
                          **contours.diagnostics}
                values[t] = f
                records.append(record)
                print(json.dumps(record),flush=True)
                data['runs'][name] = {'digits':digits,'radius':radius,'formal_order':order,
                                      'spectral_tolerance':tol,'records':records,
                                      'F':{str(t):encode(v) for t,v in values.items()}}
                checkpoint()
            tables[name] = values
        data['runs'][name]['seconds'] = perf_counter()-timing
    keys = list(tables)
    data['refinement'] = {str(t):relative(f,tables[keys[1]][t]) for t,f in tables[keys[0]].items()}
    data['source_hashes'] = {str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in (Path(__file__),Path(a.__file__),Path(a.hp.__file__),
                                       Path(a.hp.c.__file__),Path(a.hp.c.core.__file__),Path(a.hp.c.old.__file__))}
    for p,digest in hashes.items():
        if hashlib.sha256(Path(p).read_bytes()).hexdigest() != digest:
            raise RuntimeError('Protected file changed: '+p)
    data['seconds'] = perf_counter()-start
    data['mpmath_version'] = a.hp.mpm.__version__
    data['mpmath_backend'] = a.hp.mpm.libmp.BACKEND
    data['caveat'] = 'Finite-lambda B transport supplies only column normalization, never the linearized solution or a imposed conserved quantity. Refinement tests are empirical, not certified enclosures. Costs use different precisions and algorithms.'
    checkpoint()
    print('Completed in',data['seconds'],'seconds',flush=True)


if __name__ == '__main__':
    main()
