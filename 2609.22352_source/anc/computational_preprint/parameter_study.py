"""Parameter robustness, matched solution accuracy, and refinement diagnostics."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
from time import perf_counter

from mpmath import mp

import anchored_psi as ap
import high_precision as hp
import pii_core as pii
import rk45_multiprecision as rk
from compare_pii import encode


ROOT = Path(__file__).resolve().parent
CASES = {
    'pii_u015': ('PII', '.15', '.1'),
    'pii_u025': ('PII', '.25', '.1'),
    'pii_w015': ('PII', '.2', '.15'),
    'piv_theta035': ('PIV', '.35', '.11'),
    'piv_theta039': ('PIV', '.39', '.11'),
}


def norm(a):
    return max(map(abs, a))


def relative(a, b):
    return norm(a-b)/norm(b)


def metrics(values, refs, jac):
    rows = []
    for t, f in values.items():
        rows.append({'t': t, 'E': relative(f, refs[t]),
                     'D': relative(jac[t]*f, jac[0]), 'W': abs(mp.det(f)-1)})
    return {**{k: max(r[k] for r in rows) for k in ('E', 'D', 'W')}, 'points': rows}


def weighted_difference(left, right, jac):
    return max(norm(jac[t]*(left[t]-right[t]))/norm(jac[0]) for t in left)


def refinement_budget(coarse, fine, refs, jac, coarse_jac, coarse_refs):
    """Observed increments in monodromy units, not rigorous error enclosures."""
    return {
        'contour_increment': weighted_difference(fine, coarse, jac),
        'reference_increment': weighted_difference(refs, coarse_refs, jac),
        'monitor_increment': max(
            (norm((jac[t]-coarse_jac[t])*fine[t])+norm(jac[0]-coarse_jac[0]))/norm(jac[0])
            for t in fine),
        'reference_conservation_defect': metrics(refs, refs, jac)['D'],
        'max_condition_factor': max(2*norm(jac[t])*norm(refs[t])/norm(jac[0]) for t in fine),
    }


def run_case(name, destination):
    kind, a, b = CASES[name]
    mp.dps = 70
    start = perf_counter()
    points = [0, -1, -3, -6, -9, -12] if kind == 'PII' else [-6., -3., 0., .62, 3., 6.]
    record = {'case': name, 'kind': kind, 'status': 'running', 'points': points,
              'digits': 70, 'python': platform.python_version(), 'contours': [], 'rk_trials': {}}
    destination.mkdir(parents=True, exist_ok=False)

    def save():
        (destination/'results.json').write_text(json.dumps(encode(record), indent=2)+'\n')

    def log(message):
        print(name+': '+message, flush=True)
        save()

    if kind == 'PII':
        settings = {'u0': a, 'w0': b, 'x0': '-1', 'span': 12}
        make_ref = lambda digits, tol, order: pii.Reference(
            **settings, digits=digits, tolerance=tol, order=order)
        tolerances = ['1e-6', '1e-9', '1e-12']
        record['initial'] = settings
    else:
        parameters = hp.Parameters()
        parameters.a = mp.mpc(a, b)
        make_ref = lambda digits, tol, order: hp.TaylorReference(
            6, digits, tol, order, parameters=parameters)
        tolerances = ['1e-23', '1e-26', '1e-29']
        record['initial'] = {k: getattr(parameters, k) for k in ('x0','q0','h0','a','b')}
    record['reference_settings'] = [[55, '1e-27', 32], [70, '1e-36', 40]]
    coarse_ref = make_ref(55, '1e-27', 32)
    ref = make_ref(70, '1e-36', 40)
    refs = {t: ref.matrix(t) for t in points}
    coarse_refs = {t: coarse_ref.matrix(t) for t in points}
    record['reference'] = {'F': refs, 'state': {t: ref.at(t) for t in points},
                           'F_increment': max(relative(refs[t], coarse_refs[t]) for t in points),
                           'background_increment': max(norm(mp.matrix(ref.at(t)[:2])-mp.matrix(coarse_ref.at(t)[:2])) for t in points)}
    log('reference refined')
    monitors = []
    for level in (0, 1):
        jac, monodromy = {}, {}
        with mp.workdps(80+10*level):
            for t in points:
                log(f'monitor {level+1}/2 at t={t}')
                state = ref.at(t)
                if kind == 'PII':
                    s, j, defect = pii.monodromy(ref.x0+t, *state[:2], radius=5+.5*level,
                        formal_order=64+16*level, tolerance='1e-36' if level == 0 else '1e-40',
                        order=40+4*level)
                else:
                    _, s, j = hp.monodromy(ref.p.x0+mp.mpf(t), *state[:2], ref.p,
                        radius=18+level, formal_order=56+8*level,
                        tol='1e-36' if level == 0 else '1e-40')
                    j = j*hp.tangent_conversion(ref.p.x0+mp.mpf(t), state)
                jac[t], monodromy[t] = j, s
        monitors.append(jac)
        record.setdefault('monitors', []).append({'J': jac, 'm': monodromy,
            'digits': 80+10*level, 'reference_defect': metrics(refs, refs, jac)['D']})
        save()
    jac = monitors[1]
    anchors = {n: ap.AnchorTransport(ref, mp.mpf('1.45')*s) for n,s in [('A',1),('B',-1)]} if kind == 'PIV' else None
    values_by_level = []
    # Three fixed levels make the refinement test reproducible across cases.
    for tolerance in tolerances:
        log('contour tolerance '+tolerance)
        stamp = perf_counter()
        contours = (pii.Contours(ref, radius=4, formal_order=48, tolerance=tolerance)
                    if kind == 'PII' else ap.AnchoredContours(ref, radius=14, formal_order=40,
                                                          tolerance=tolerance, anchors=anchors))
        values, diagnostics = {}, {}
        for t in points:
            if kind == 'PII':
                values[t], diagnostics[t] = contours.at(t)
            else:
                values[t] = contours.at(t)
                diagnostics[t] = dict(contours.diagnostics)
        values_by_level.append(values)
        record['contours'].append({'tolerance': tolerance, 'F': values, 'diagnostics': diagnostics,
                                  'seconds': perf_counter()-stamp, **metrics(values, refs, jac)})
        log('contour E='+mp.nstr(record['contours'][-1]['E'], 5))
    record['refinement'] = refinement_budget(values_by_level[-2], values_by_level[-1],
                                             refs, jac, monitors[0], coarse_refs)
    record['refinement']['previous_contour_increment'] = weighted_difference(
        values_by_level[0], values_by_level[1], jac)
    record['refinement']['contraction'] = (record['refinement']['contour_increment']/
                                         record['refinement']['previous_contour_increment'])
    # Compare the middle level: the finest level is an independent refinement.
    target = record['contours'][1]['E']
    tol = target/10
    for _ in range(10):
        key = mp.nstr(tol, 14)
        log('RK tolerance '+key)
        if key not in record['rk_trials']:
            stamp = perf_counter()
            if kind == 'PII':
                def rhs(t, y):
                    u = ref.potential(t)
                    return [y[1], u*y[0], y[3], u*y[2]]
                states, stats = rk.integrate(rhs, points, list(map(mp.mpf, [1,0,0,1])), key)
                values = {t: mp.matrix([[s[0],s[2]],[s[1],s[3]]]) for t,s in states.items()}
            else:
                values, stats = rk.fundamental(ref, points, key)
            record['rk_trials'][key] = {**stats, 'seconds': perf_counter()-stamp,
                                       'F': values, **metrics(values, refs, jac)}
        ratio = record['rk_trials'][key]['E']/target
        if 1/mp.mpf('1.1') <= ratio <= mp.mpf('1.1'):
            break
        tol = mp.mpf(key)/ratio
    best = min(record['rk_trials'], key=lambda k: abs(mp.log(record['rk_trials'][k]['E']/target)))
    trial = record['rk_trials'][best]
    ratio = trial['E']/target
    record['pair'] = {'contour_level': 1, 'rk_tolerance': best,
                      'matched': bool(1/mp.mpf('1.1') <= ratio <= mp.mpf('1.1')),
                      'E_ratio': ratio, 'D_ratio': trial['D']/record['contours'][1]['D']}
    budget = record['refinement']
    floor = max(budget['reference_increment'], budget['monitor_increment'], budget['reference_conservation_defect'])
    signal = min(trial['D'], record['contours'][1]['D'])
    record['resolved'] = bool(floor < signal/100)
    record['status'] = 'complete' if record['resolved'] and record['pair']['matched'] else 'needs_refinement'
    record['total_seconds'] = perf_counter()-start
    record['source_hashes'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
                              [Path(__file__), ROOT/'high_precision.py', ROOT/'pii_core.py',
                               ROOT/'anchored_psi.py', ROOT/'rk45_multiprecision.py']}
    log(f"{record['status']}: drift ratio="+mp.nstr(record['pair']['D_ratio'], 6))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cases', nargs='+', choices=CASES, default=list(CASES))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    for name in args.cases:
        run_case(name, args.output/name)


if __name__ == '__main__':
    main()
