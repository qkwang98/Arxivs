#!/usr/bin/env python3
"""Match achieved errors with common background and 70-digit arithmetic."""
import argparse
import hashlib
import json
import math
from pathlib import Path
from time import perf_counter

from mpmath import mp

import anchored_psi as anchored
import rk45_multiprecision as rk
from run_anchored import decode
from run_stabilized import encode,relative


POINTS = [-6.,-3.,0.,.62,3.,6.]


def metrics(values,reference,jac):
    rows = []
    for t in POINTS:
        f,ff = values[t],reference.matrix(t)
        rows.append({'t':t,'solution_error':relative(f,ff),
                     'variation_drift':relative(jac[t]*f,jac[0.]),
                     'wronskian_error':float(abs(mp.det(f)-1))})
    return {'max_solution_error':max(row['solution_error'] for row in rows),
            'max_variation_drift':max(row['variation_drift'] for row in rows),
            'max_wronskian_error':max(row['wronskian_error'] for row in rows),'points':rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'results/equal_accuracy')
    parser.add_argument('--radii',nargs='+',type=float,default=[13.5,14.])
    parser.add_argument('--spectral-tolerance',default='1e-26')
    parser.add_argument('--match-factor',type=float,default=1.5)
    parser.add_argument('--reuse-contours',type=Path)
    args = parser.parse_args()
    if args.match_factor <= 1 or mp.mpf(args.spectral_tolerance) <= 0:
        parser.error('Use match-factor > 1 and a positive spectral tolerance')
    args.output.mkdir(parents=True,exist_ok=False)
    mp.dps = 70
    total_start = perf_counter()
    source = Path(__file__).parent/'results/stabilized_long/results.json'
    saved = json.loads(source.read_text())
    jac = {t:decode(saved['runs']['dps80_R18_N56']['values'][str(t)]['J']) for t in POINTS}
    protected = [rk.hp.c.ROOT/'piv2026_manuscript.tex',rk.hp.c.ROOT/'ms_source.zip',
                 rk.hp.c.ROOT/'ms_submission.zip',*sorted((rk.hp.c.ROOT/'verification').glob('*'))]
    hashes = {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in protected if p.is_file()}
    data = {'digits':70,'span':6,'points':POINTS,'matching_rule':
            'Max of pointwise relative max-entry errors on the same six points; accepted ratio 2/3 to 3/2. Monodromy is never used for matching.',
            'rk_trials':{},'contours':{},'pairs':{},'shared_costs':{},'protected_hashes':hashes,
            'match_factor':args.match_factor}
    data['matching_rule'] = ('Max of pointwise relative max-entry errors on the same six points; '
                             f'accepted error ratio 1/{args.match_factor} to {args.match_factor}. '
                             'Monodromy is never used for matching.')
    def checkpoint():
        (args.output/'results.json').write_text(json.dumps(data,indent=2)+'\n')
    print('Common 70-digit background and reference',flush=True)
    start = perf_counter()
    reference = rk.hp.TaylorReference(6,70,'1e-36',40)
    data['shared_costs']['background_and_reference_seconds'] = perf_counter()-start
    refs = {t:reference.matrix(t) for t in POINTS}
    data['reference_monitor_drift'] = metrics(refs,reference,jac)['max_variation_drift']
    data['reference_values'] = {str(t):encode(f) for t,f in refs.items()}
    data['shared_monitor_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
    data['shared_monitor_status'] = 'Previously independently computed; common evaluation, no invariant projection.'
    trials = {}
    def trial(tol):
        key = mp.nstr(mp.mpf(tol),14)
        if key not in trials:
            print('RK45 MP tolerance',key,flush=True)
            values,cost = rk.fundamental(reference,POINTS,key)
            record = {**cost,**metrics(values,reference,jac),'F':{str(t):encode(values[t]) for t in POINTS}}
            data['rk_trials'][key] = record
            trials[key] = values
            print(json.dumps({k:v for k,v in record.items() if k not in ('points','F')}),flush=True)
            checkpoint()
        return key
    trial('1e-12')
    reused = json.loads(args.reuse_contours.read_text()) if args.reuse_contours else None
    if reused:
        if reused['digits'] != 70 or reused['points'] != POINTS:
            raise ValueError('Reused contours have different precision or sample points')
        for t in POINTS:
            if relative(decode(reused['reference_values'][str(t)]),reference.matrix(t)) > 1e-30:
                raise ValueError('Reused contour background/reference does not match')
        anchors = None
        anchor_seconds = reused['anchor_preparation_seconds']
        data['reused_contours_sha256'] = hashlib.sha256(args.reuse_contours.read_bytes()).hexdigest()
    else:
        print('Finite-lambda normalizations (charged to contours)',flush=True)
        start = perf_counter()
        anchors = {name:anchored.AnchorTransport(reference,mp.mpf('1.45')*(1 if name == 'A' else -1)) for name in ('A','B')}
        anchor_seconds = perf_counter()-start
    data['anchor_preparation_seconds'] = anchor_seconds
    for radius in args.radii:
        name = f'R{radius}_N40_tol{args.spectral_tolerance}'
        print('Contour',name,flush=True)
        start = perf_counter()
        if reused:
            record = reused['contours'][name]
        else:
            method = anchored.AnchoredContours(reference,radius,40,args.spectral_tolerance,anchors)
            values,diagnostics = {},{}
            for t in POINTS:
                print(f'  t={t:g}',flush=True)
                values[t] = method.at(t)
                diagnostics[str(t)] = method.diagnostics
            evaluation_seconds = perf_counter()-start
            record = {**metrics(values,reference,jac),'radius':radius,'formal_order':40,
                      'spectral_tolerance':args.spectral_tolerance,'digits':mp.dps,
                      'evaluation_seconds':evaluation_seconds,
                      'standalone_seconds':evaluation_seconds+anchor_seconds,
                      'anchor_diagnostics':diagnostics,
                      'F':{str(t):encode(v) for t,v in values.items()}}
        data['contours'][name] = record
        target = record['max_solution_error']
        print('Contour max error and drift:',target,record['max_variation_drift'],flush=True)
        checkpoint()
        selected = None
        for _ in range(5):
            selected = min(data['rk_trials'],key=lambda key:abs(math.log(data['rk_trials'][key]['max_solution_error']/target)))
            achieved = data['rk_trials'][selected]['max_solution_error']
            if 1/args.match_factor <= achieved/target <= args.match_factor:
                break
            correction = min(1000,max(.001,target/achieved))
            trial(mp.mpf(selected)*mp.mpf(str(correction)))
        selected = min(data['rk_trials'],key=lambda key:abs(math.log(data['rk_trials'][key]['max_solution_error']/target)))
        rr = data['rk_trials'][selected]
        ratio = rr['max_solution_error']/target
        data['pairs'][name] = {'rk_tolerance':selected,'matched':1/args.match_factor <= ratio <= args.match_factor,
                              'rk_to_contour_error_ratio':ratio,
                              'rk_to_contour_drift_ratio':rr['max_variation_drift']/record['max_variation_drift'],
                              'contour_to_rk_cost_ratio':record['standalone_seconds']/rr['seconds']}
        print('Pair',json.dumps(data['pairs'][name]),flush=True)
        checkpoint()
    for path,digest in hashes.items():
        if hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest:
            raise RuntimeError('Protected file changed: '+path)
    data['source_hashes'] = {str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in (Path(__file__),Path(rk.__file__),Path(anchored.__file__),Path(rk.hp.__file__),Path(rk.hp.c.__file__))}
    data['mpmath_version'] = rk.hp.mpm.__version__
    data['mpmath_backend'] = rk.hp.mpm.libmp.BACKEND
    data['seconds'] = perf_counter()-total_start
    data['caveats'] = [
        'Six-node error criterion, not a rigorous bound over the interval.',
        'One background and two contour truncations; no broad performance claim.',
        'Timing is a single run; common background/reference and cached monitor costs excluded from both methods.',
        'Each contour standalone cost includes all finite-lambda preparation, even when reused in the sweep.',
        'Matching excludes calibration cost from the selected solver run; all calibration trials and total time are preserved.',
        'Equal maximal solution errors need not mean equal pointwise error distributions.',
        'Dormand-Prince 5(4) is implemented with mp arithmetic, exact rational tableau, RMS controller, and steps ending at output nodes; it is not a call to float64 scipy.solve_ivp.',
        'mp RK stages evaluate q from the common reference coefficients; the reference F is used only for diagnostics and tolerance calibration.']
    checkpoint()
    print('Completed in',data['seconds'],'seconds',flush=True)


if __name__ == '__main__':
    main()
