#!/usr/bin/env python3
"""Refine the background, canonical columns, contours, and monodromy monitor."""
import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter

import numpy as np
from mpmath import mp

import high_precision as hp


def maxabs(matrix):
    return max(abs(v) for v in matrix)


def relative(left,right):
    return float(maxabs(left-right)/max(maxabs(right),mp.mpf('1e-80')))


def encode(matrix):
    return [[[mp.nstr(matrix[i,j].real,80),mp.nstr(matrix[i,j].imag,80)]
             for j in range(matrix.cols)] for i in range(matrix.rows)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'results/stabilized_long')
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    mp.dps = 80
    start = perf_counter()
    data = {'reference':{},'runs':{},'comparisons':{}}
    def checkpoint():
        (args.output/'results.json').write_text(json.dumps(data,indent=2)+'\n')
    print('Reference: 50 digits',flush=True)
    low = hp.TaylorReference(6,50,'1e-26',32)
    print('Reference: 70 digits',flush=True)
    ref = hp.TaylorReference(6,70,'1e-36',40)
    saved = np.load(Path(__file__).parent/'results/long_interval_6/arrays.npz')
    grid = saved['grid']
    points = [-6.,-3.,0.,.62,3.,6.]
    matrices = {float(t):ref.matrix(float(t)) for t in grid}
    qerrors, ferrors, werrors, olderrors = [],[],[],[]
    for i,t in enumerate(grid):
        state, slo = ref.at(float(t)),low.at(float(t))
        f = matrices[float(t)]
        qerrors.append(float(abs(state[0]-slo[0])/max(1,abs(state[0]))))
        ferrors.append(relative(low.matrix(float(t)),f))
        werrors.append(float(abs(mp.det(f)-1)))
        olderrors.append(relative(mp.matrix(saved['reference'][i].tolist()),f))
    data['reference'] = {'low_digits':50,'high_digits':70,'low_tolerance':'1e-26',
                         'high_tolerance':'1e-36','low_steps':low.cost,'high_steps':ref.cost,
                         'max_q_refinement':max(qerrors),'max_pointwise_F_refinement':max(ferrors),
                         'max_wronskian_error':max(werrors),'max_old_reference_error':max(olderrors),
                         'grid':grid.tolist(),'old_reference_pointwise_errors':olderrors,
                         'values':{str(t):{'state':encode(mp.matrix(ref.at(t))),
                                          'F':encode(matrices[t])} for t in points}}
    print(json.dumps({k:v for k,v in data['reference'].items() if k not in ('values','grid','old_reference_pointwise_errors')}),flush=True)
    checkpoint()
    rk = {}
    for tol in (1e-9,1e-12):
        f,cost = hp.c.rk_matrix(grid,lambda t:[ref.q_float(t),0,0],tol,'RK45')
        name = f'RK45_hp_background_{tol}'
        rk[name] = {float(t):mp.matrix(f[i].tolist()) for i,t in enumerate(grid)}
        data['comparisons'][name] = {**cost,'max_pointwise_solution_error':max(relative(rk[name][float(t)],matrices[float(t)]) for t in grid)}
    rk['RK45_old_background_1e-12'] = {float(t):mp.matrix(saved['RK45_1e-12'][i].tolist()) for i,t in enumerate(grid)}
    data['comparisons']['RK45_old_background_1e-12'] = {
        'max_pointwise_solution_error':max(relative(rk['RK45_old_background_1e-12'][float(t)],matrices[float(t)]) for t in grid)}
    results = {}
    for digits,radius,order,tol in ((60,14,40,'1e-26'),(80,18,56,'1e-36')):
        name = f'dps{digits}_R{radius}_N{order}'
        print(f'Stabilized run {name}',flush=True)
        timing = perf_counter()
        with mp.workdps(digits):
            p = ref.p
            initial = ref.at(0)
            phi0,coefficients = hp.contour_basis(p.x0,initial,p,radius,order,tol)
            inverse = phi0**-1
            _,m0,jqh0 = hp.monodromy(p.x0,*initial[:2],p,radius,order,tol)
            j0 = jqh0*hp.tangent_conversion(p.x0,initial)
            records,values = [],{}
            for t in points:
                print(f'  t={t:g}',flush=True)
                state = ref.at(t)
                x = p.x0+mp.mpf(t)
                if t == 0:
                    f,m,j = mp.eye(2),m0,j0
                else:
                    phi,_ = hp.contour_basis(x,state,p,radius,order,tol,coefficients)
                    f = phi*inverse
                    _,m,jqh = hp.monodromy(x,*state[:2],p,radius,order,tol)
                    j = jqh*hp.tangent_conversion(x,state)
                ff = matrices[t]
                record = {'t':t,'contour_solution_error':relative(f,ff),
                          'invariant_drift':relative(m,m0),
                          'monitor_drift_on_reference':relative(j*ff,j0),
                          'contour_variation_drift':relative(j*f,j0),
                          'contour_wronskian_error':float(abs(mp.det(f)-1)),
                          'rk':{key:{'solution_error':relative(table[t],ff),
                                     'variation_drift':relative(j*table[t],j0)} for key,table in rk.items()}}
                values[t] = {'F':f,'m':m,'J':j}
                records.append(record)
                print(json.dumps(record),flush=True)
                data['runs'][name] = {'digits':digits,'radius':radius,'formal_order':order,
                                      'spectral_tolerance':tol,'records':records,
                                      'values':{str(t):{key:encode(value) for key,value in v.items()} for t,v in values.items()}}
                checkpoint()
            data['runs'][name]['seconds'] = perf_counter()-timing
            results[name] = values
    keys = list(results)
    data['refinement'] = {str(t):{key:relative(results[keys[0]][t][key],results[keys[1]][t][key])
                                 for key in ('F','m','J')} for t in points}
    data['seconds'] = perf_counter()-start
    data['mpmath_version'] = hp.mpm.__version__
    data['mpmath_backend'] = hp.mpm.libmp.BACKEND
    data['numpy_version'],data['scipy_version'] = np.__version__,hp.c.scipy.__version__
    data['source_hashes'] = {str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in (Path(__file__),Path(hp.__file__),Path(hp.c.__file__),Path(hp.c.core.__file__),Path(hp.c.old.__file__))}
    data['caveat'] = 'No interval certification. Spectral and reference Taylor recurrences differ, but share the arithmetic library and model parameters. Pointwise drift tests do not bound the whole continuum.'
    checkpoint()
    print('Completed; total seconds:',data['seconds'],flush=True)


if __name__ == '__main__':
    main()
