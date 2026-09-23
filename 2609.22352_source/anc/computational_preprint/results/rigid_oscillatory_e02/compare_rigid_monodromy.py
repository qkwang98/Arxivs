#!/usr/bin/env python3
"""Independent Stokes-variation conservation test through a rigid PII pulse."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from time import perf_counter

from mpmath import mp

from compare_pii import encode,relative
import rigid_monodromy as r
import rk45_multiprecision as rk


ROOT = Path(__file__).resolve().parent


def row_relative(a,b):
    return [float(max(abs(a[j,k]-b[j,k]) for k in range(b.cols))/max(abs(b[j,k]) for k in range(b.cols)))
            for j in range(b.rows)]


def metrics(values,ref,offsets,jac):
    out = []
    for offset in offsets:
        t = ref.t0+mp.mpf(offset)
        f = values[offset]
        rows = row_relative(jac[offset]*f,jac[0.])
        out.append({'offset':offset,'t':float(t),'solution_error':relative(f,ref.matrix(t)),
                    'variation_drift':relative(jac[offset]*f,jac[0.]),'row_variation_drift':rows,
                    'max_row_variation_drift':max(rows),'wronskian_error':float(abs(mp.det(f)-1))})
    return {**{'max_'+key:max(v[key] for v in out) for key in ('solution_error','variation_drift','wronskian_error')},
            'max_row_variation_drift':max(v['max_row_variation_drift'] for v in out),'points':out}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=ROOT/'results/rigid_stokes_e02')
    parser.add_argument('--epsilon',default='.2')
    parser.add_argument('--peak-guess',default='-1.623')
    parser.add_argument('--contour-tolerances',nargs='*',default=['1e-14','1e-18'])
    parser.add_argument('--reuse-monitor',type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    total = perf_counter()
    mp.dps = 100
    for file in ('compare_rigid_monodromy.py','rigid_monodromy.py','rk45_multiprecision.py',
                 'pii_core.py','high_precision.py','test_rigid_monodromy.py'):
        shutil.copy2(ROOT/file,args.output/file)
    previous = json.loads((ROOT/'results/pii_comparison/results.json').read_text())
    protected = list(previous['protected_hashes'])+['<arXiv:solv-int/9902007v1.pdf>']
    hashes = {path:hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in protected}
    data = {'status':'running','epsilon':args.epsilon,'comparison_digits':90,
            'monitor_settings':{'digits':100,'radius':8,'formal_order':80,'tolerance':'1e-32','order':40,'vertex':'1.5'},
            'protected_hashes':hashes,'monitor':{},'rk_trials':{},'contours':{},'pairs':{}}
    def save():
        (args.output/'results.json').write_text(json.dumps(encode(data),indent=2)+'\n')
    print('High-precision common background and tangent reference',flush=True)
    start = perf_counter()
    ref = r.Reference(epsilon=args.epsilon)
    peak = ref.peak(args.peak_guess)
    astar = -2**(-mp.mpf(2)/3)
    tstar = -6*astar*astar
    # RK's generic integrator uses binary output offsets. Use those same
    # exact offsets for every reference and spectral evaluation as well.
    offsets = [0.,float(tstar-ref.t0),float(peak-ref.epsilon/2-ref.t0),
               float(peak-ref.t0),float(peak+ref.epsilon-ref.t0),6.]
    data['offsets'],data['peak'],data['t_star'] = offsets,peak,tstar
    data['reference'] = {'seconds':perf_counter()-start,'steps':len(ref.segments),
                          'F':{s:ref.matrix(ref.t0+mp.mpf(s)) for s in offsets},
                          'state':{s:ref.at(ref.t0+mp.mpf(s)) for s in offsets}}
    coarse = r.Reference(epsilon=args.epsilon,digits=65,tolerance='1e-27',order=32)
    data['reference']['refinement_error'] = max(relative(coarse.matrix(ref.t0+mp.mpf(s)),ref.matrix(ref.t0+mp.mpf(s))) for s in offsets)
    jac,stokes = {},{}
    settings = dict(radius=8,formal_order=80,tolerance='1e-32',order=40,vertex='1.5')
    start = perf_counter()
    def decode(raw):
        return mp.matrix([[mp.mpc(*v) if isinstance(v,list) else mp.mpf(v) for v in row] for row in raw])
    if args.reuse_monitor:
        old = json.loads(args.reuse_monitor.read_text())
        if old['epsilon'] != args.epsilon or old['offsets'] != offsets:
            raise ValueError('Reused monitor background/points differ')
        for offset in offsets:
            if relative(decode(old['reference']['F'][str(offset)]),ref.matrix(ref.t0+mp.mpf(offset))) > 1e-35:
                raise ValueError('Reference changed for reused monitor')
            record = old['monitor'][str(offset)]
            stokes[offset],jac[offset] = decode(record['s']),decode(record['J'])
        data['monitor'] = old['monitor']
        data['monitor_refinements'] = old['monitor_refinements']
        data['reused_monitor_sha256'] = hashlib.sha256(args.reuse_monitor.read_bytes()).hexdigest()
    else:
        for offset in offsets:
            t = ref.t0+mp.mpf(offset)
            print('Fresh Stokes coefficients and sensitivities at t=',mp.nstr(t,12),flush=True)
            s,j,diagnostic = r.monodromy(ref,t,**settings)
            stokes[offset],jac[offset] = s,j
            data['monitor'][offset] = {'s':s,'J':j,'diagnostic':diagnostic,
                                       'row_reference_variation_drift':row_relative(j*ref.matrix(t),jac[0.])}
            print('  reference row drift',data['monitor'][offset]['row_reference_variation_drift'],flush=True)
            save()
        data['monitor_refinements'] = {}
        with mp.workdps(120):
            for offset in (offsets[0],offsets[3]):
                t = ref.t0+mp.mpf(offset)
                print('Refine independent monitor at t=',mp.nstr(t,12),flush=True)
                s,j,diagnostic = r.monodromy(ref,t,radius=10,formal_order=112,tolerance='1e-42',order=44,vertex='1.5')
                data['monitor_refinements'][offset] = {'s_relative':row_relative(s,stokes[offset]),
                                                       'J_row_relative':row_relative(j,jac[offset]),
                                                       'diagnostic':diagnostic,'s':s,'J':j}
                save()
    data['monitor_seconds'] = perf_counter()-start
    data['reference_monitor'] = metrics({s:ref.matrix(ref.t0+mp.mpf(s)) for s in offsets},ref,offsets,jac)
    data['stokes_relative_drift_by_row'] = [max(row_relative(s,stokes[0.])[j] for s in stokes.values()) for j in range(4)]
    save()
    trials = {}
    def trial(tolerance):
        key = mp.nstr(mp.mpf(tolerance),14)
        if key not in trials:
            print('RK tolerance',key,flush=True)
            with mp.workdps(90):
                start = perf_counter()
                def rhs(offset,y):
                    potential = ref.potential(ref.t0+offset)
                    eps = ref.epsilon
                    return [y[1]/eps,-potential*y[0]/eps,y[3]/eps,-potential*y[2]/eps]
                states,stats = rk.integrate(rhs,offsets,list(map(mp.mpf,[1,0,0,1])),key)
                seconds = perf_counter()-start
                values = {s:mp.matrix([[y[0],y[2]],[y[1],y[3]]]) for s,y in states.items()}
                record = {**metrics(values,ref,offsets,jac),'seconds':seconds,**stats,'F':values}
            trials[key] = values
            data['rk_trials'][key] = record
            print('  E',record['max_solution_error'],'D rows',record['max_row_variation_drift'],flush=True)
            save()
        return key
    for tolerance in ('1e-8','1e-10','1e-12','1e-14'):
        trial(tolerance)
    for tolerance in args.contour_tolerances:
        print('Contour quadrature tolerance',tolerance,flush=True)
        with mp.workdps(90):
            start = perf_counter()
            method = r.Contours(ref,radius=8,formal_order=80,tolerance=tolerance,order=40,vertex='1.5')
            values,diagnostics = {},{}
            for offset in offsets:
                t = ref.t0+mp.mpf(offset)
                print('  contour t=',mp.nstr(t,12),flush=True)
                values[offset],diagnostics[offset] = method.at(t)
            seconds = perf_counter()-start
            record = {**metrics(values,ref,offsets,jac),'seconds':seconds,'F':values,'diagnostics':diagnostics,
                      'raw_initial_F':method.initial,'raw_initial_W':mp.det(method.initial),'weights':method.weights}
        data['contours'][tolerance] = record
        target = mp.mpf(record['max_solution_error'])
        print('  contour E',mp.nstr(target,9),'D rows',record['max_row_variation_drift'],flush=True)
        for _ in range(8):
            best = min(data['rk_trials'],key=lambda key:abs(mp.log(mp.mpf(data['rk_trials'][key]['max_solution_error'])/target)))
            ratio = mp.mpf(data['rk_trials'][best]['max_solution_error'])/target
            if 1/mp.mpf('1.1') <= ratio <= mp.mpf('1.1'):
                break
            trial(mp.mpf(best)/ratio)
        best = min(data['rk_trials'],key=lambda key:abs(mp.log(mp.mpf(data['rk_trials'][key]['max_solution_error'])/target)))
        ratio = data['rk_trials'][best]['max_solution_error']/float(target)
        matched = 1/1.1 <= ratio <= 1.1
        data['pairs'][tolerance] = {'rk_tolerance':best,'matched':matched,'error_ratio_RK_over_contour':ratio,
                                    'row_drift_ratio_RK_over_contour':data['rk_trials'][best]['max_row_variation_drift']/record['max_row_variation_drift'],
                                    'time_ratio_contour_over_RK':seconds/data['rk_trials'][best]['seconds']}
        save()
    data['protected_unchanged'] = all(hashlib.sha256(Path(path).read_bytes()).hexdigest()==h for path,h in hashes.items())
    data['total_seconds'] = perf_counter()-total
    data['status'] = 'complete'
    save()
    print(json.dumps({'pairs':data['pairs'],'monitor_floor_by_rows':data['reference_monitor']['max_row_variation_drift'],
                       'seconds':data['total_seconds'],'protected_unchanged':data['protected_unchanged']},indent=2),flush=True)


if __name__ == '__main__':
    main()
