#!/usr/bin/env python3
"""First matched-accuracy PII comparison; independent Stokes sensitivities."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from time import perf_counter

from mpmath import mp

import pii_core as p
import rk45_multiprecision as rk


POINTS = [0, -1, -3, -6, -9, -12]
ROOT = Path(__file__).resolve().parent
SOURCE = Path('<RCD-2024-source>')


def encode(value):
    if isinstance(value, mp.matrix):
        return [[encode(value[i,j]) for j in range(value.cols)] for i in range(value.rows)]
    if isinstance(value, dict):
        return {str(k): encode(v) for k,v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    if isinstance(value, mp.mpc):
        return [mp.nstr(value.real, 80), mp.nstr(value.imag, 80)]
    if isinstance(value, mp.mpf):
        return mp.nstr(value, 80)
    return value


def relative(a, b):
    return float(max(map(abs, a-b))/max(map(abs, b)))


def metrics(values, ref, jac):
    rows = [{'t':t, 'x':float(ref.x0+t), 'solution_error':relative(values[t],ref.matrix(t)),
             'variation_drift':relative(jac[t]*values[t],jac[0]),
             'wronskian_error':float(abs(mp.det(values[t])-1))} for t in POINTS]
    return {**{'max_'+key:max(row[key] for row in rows)
               for key in ('solution_error','variation_drift','wronskian_error')}, 'points':rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT/'results/pii_first')
    parser.add_argument('--spectral-tolerances', nargs='+', default=['1e-9','1e-12'])
    parser.add_argument('--match-factor', type=float, default=1.1)
    args = parser.parse_args()
    if args.match_factor <= 1:
        parser.error('match-factor must exceed one')
    args.output.mkdir(parents=True, exist_ok=False)
    mp.dps = 70
    start_all = perf_counter()
    protected = [SOURCE, ROOT.parent/'piv2026_manuscript.tex',
                 ROOT.parent/'ms_source.zip', ROOT.parent/'ms_submission.zip',
                 *sorted((ROOT.parent/'verification').glob('*'))]
    hashes = {str(v):hashlib.sha256(v.read_bytes()).hexdigest() for v in protected if v.is_file()}
    data = {'equation':'u_xx=2*u^3+x*u; alpha=0', 'initial':{'x0':'-1','u0':'.2','w0':'.1'},
            'points':POINTS, 'digits':70, 'protected_hashes':hashes,
            'matching_rule':'Max pointwise relative max-entry error in F, same six points; monodromy not used in matching.',
            'match_factor':args.match_factor,'contours':{},'rk_trials':{},'pairs':{}}
    for name in ('compare_pii.py','pii_core.py','rk45_multiprecision.py','high_precision.py','test_pii.py'):
        shutil.copy2(ROOT/name, args.output/name)
    def checkpoint():
        (args.output/'results.json').write_text(json.dumps(encode(data),indent=2)+'\n')
    print('PII: two independently refined Taylor references', flush=True)
    start = perf_counter()
    coarse = p.Reference(digits=50, tolerance='1e-26', order=32)
    ref = p.Reference()
    data['reference'] = {'seconds':perf_counter()-start,
                         'refinement_F':max(relative(coarse.matrix(t),ref.matrix(t)) for t in POINTS),
                         'refinement_u_absolute':float(max(abs(coarse.at(t)[0]-ref.at(t)[0]) for t in POINTS)),
                         'steps':len(ref.segments), 'F':{t:ref.matrix(t) for t in POINTS},
                         'state':{t:ref.at(t) for t in POINTS}}
    jac, stokes = {}, {}
    start = perf_counter()
    with mp.workdps(80):
        for t in POINTS:
            print(f'  independent Stokes monitor x={ref.x0+t}',flush=True)
            s,j,defect = p.monodromy(ref.x0+t,*ref.at(t)[:2],radius=5,formal_order=64,
                                     tolerance='1e-36',order=40)
            jac[t],stokes[t] = j,s
            data.setdefault('monitor',{})[t] = {'s':s,'J':j,'adjacent_determinant_defect':defect}
            checkpoint()
        s,j,defect = p.monodromy(ref.x0-12,*ref.at(-12)[:2],radius=5.5,formal_order=80,
                                 tolerance='1e-40',order=44)
        data['monitor_refinement_at_minus13'] = {'s_absolute':float(max(map(abs,s-stokes[-12]))),
                                                 'J_relative':relative(j,jac[-12]),
                                                 'adjacent_determinant_defect':float(defect)}
    data['monitor_seconds'] = perf_counter()-start
    data['monitor_stokes_drift_absolute'] = float(max(max(map(abs,s-stokes[0])) for s in stokes.values()))
    data['monitor_reference_variation_drift'] = metrics({t:ref.matrix(t) for t in POINTS},ref,jac)['max_variation_drift']
    trials = {}
    def trial(tol):
        key = mp.nstr(mp.mpf(tol),14)
        if key not in trials:
            start = perf_counter()
            def rhs(t,y):
                potential = ref.potential(t)
                return [y[1],potential*y[0],y[3],potential*y[2]]
            states, stats = rk.integrate(rhs,POINTS,list(map(mp.mpf,[1,0,0,1])),key)
            elapsed = perf_counter()-start
            values = {t:mp.matrix([[s[0],s[2]],[s[1],s[3]]]) for t,s in states.items()}
            trials[key] = values
            data['rk_trials'][key] = {**metrics(values,ref,jac),**stats,'seconds':elapsed,'F':values}
            print('  RK',key,'E',data['rk_trials'][key]['max_solution_error'],flush=True)
            checkpoint()
        return key
    for tolerance in args.spectral_tolerances:
        print('Contour tolerance',tolerance,flush=True)
        start = perf_counter()
        contours = p.Contours(ref,radius=4,formal_order=48,tolerance=tolerance)
        values, diagnostics = {}, {}
        for t in POINTS:
            values[t], diagnostics[t] = contours.at(t)
        elapsed = perf_counter()-start
        record = {**metrics(values,ref,jac), 'seconds':elapsed,'F':values,'diagnostics':diagnostics,
                  'initial_raw_F':contours.initial_matrix,'raw_W':mp.det(contours.initial_matrix),
                  'weights':contours.weights,'radius':4,'formal_order':48,'spectral_tolerance':tolerance}
        data['contours'][tolerance] = record
        target = mp.mpf(record['max_solution_error'])
        print('  contour E',target,flush=True)
        tol = target/10
        for iteration in range(10):
            key = trial(tol)
            ratio = mp.mpf(data['rk_trials'][key]['max_solution_error'])/target
            if 1/args.match_factor <= ratio <= args.match_factor:
                break
            tol = mp.mpf(key)/ratio
        best = min(data['rk_trials'],key=lambda k: abs(mp.log(mp.mpf(data['rk_trials'][k]['max_solution_error'])/target)))
        selected = data['rk_trials'][best]
        ratio = selected['max_solution_error']/float(target)
        data['pairs'][tolerance] = {'rk_tolerance':best,'error_ratio_RK_over_contour':ratio,
                                    'matched':1/args.match_factor <= ratio <= args.match_factor,
                                    'drift_ratio_RK_over_contour':selected['max_variation_drift']/record['max_variation_drift'],
                                    'cost_ratio_contour_over_RK':elapsed/selected['seconds']}
        checkpoint()
    print('Independent finite-difference residual from contour values',flush=True)
    fine = p.Contours(ref,radius=4,formal_order=48,tolerance='1e-26')
    center, h = mp.mpf(-6), mp.mpf('0.001')
    values = {k:fine.at(center+k*h/2)[0] for k in (-4,-2,-1,0,1,2,4)}
    residuals = {}
    for stride in (2,1):
        step = stride*h/2
        d2 = (-values[2*stride]+16*values[stride]-30*values[0]+16*values[-stride]-values[-2*stride])/(12*step*step)
        potential = ref.potential(center)
        residuals[str(step)] = float(max(abs(d2[0,j]-potential*values[0][0,j]) for j in range(2))/
                                     max(1,max(abs(potential*values[0][0,j]) for j in range(2))))
    data['finite_difference_residual'] = {'x':str(ref.x0+center),'relative_by_step':residuals,
                                         'spectral_tolerance':'1e-26',
                                         'note':'Centered five-point second derivative of contour values; denominator max(1, |potential*F_row1|).'}
    data['total_seconds'] = perf_counter()-start_all
    data['protected_unchanged'] = all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == old for path,old in hashes.items())
    checkpoint()
    print(json.dumps({'pairs':data['pairs'],'monitor_floor':data['monitor_reference_variation_drift'],
                       'residual':data['finite_difference_residual'],'seconds':data['total_seconds'],
                       'protected_unchanged':data['protected_unchanged']},indent=2),flush=True)


if __name__ == '__main__':
    main()
