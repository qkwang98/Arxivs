"""Follow Stokes variations from the algebraic branch to regular oscillations."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from time import perf_counter

from mpmath import mp

from compare_pii import encode, relative
from compare_rigid_monodromy import metrics, row_relative
import rigid_monodromy as r
import rk45_multiprecision as rk


ROOT = Path(__file__).resolve().parent


def decode(raw):
    return mp.matrix([[mp.mpc(*v) if isinstance(v, list) else mp.mpf(v)
                       for v in row] for row in raw])


def maxima(ref, spacing='.01'):
    out = []
    left = max(ref.t0, mp.mpf('-2'))
    step = mp.mpf(spacing)
    lp = ref.at(left)[1]
    while left < ref.end:
        right = min(left+step, ref.end)
        rp = ref.at(right)[1]
        if lp > 0 and rp <= 0:
            t = mp.findroot(lambda s: ref.at(s)[1], (left, right),
                            solver='anderson', tol=mp.mpf('1e-50'))
            record = {'t': t, 'u': ref.at(t)[0]}
            if out:
                record['period'] = t-out[-1]['t']
                record['relative_height_change'] = abs(record['u']/out[-1]['u']-1)
            if len(out) >= 2:
                record['relative_period_change'] = abs(record['period']/out[-1]['period']-1)
            out.append(record)
        left, lp = right, rp
    return out


def post_drift(values, jac, offsets, entry):
    origin = jac[0.]
    constant_at_entry = jac[entry]*values[entry]
    points = []
    for offset in offsets:
        if offset < entry:
            continue
        difference = jac[offset]*values[offset]-constant_at_entry
        rows = row_relative(origin+difference, origin)
        points.append({'offset': offset, 't': offset-7,
                       'rows': rows, 'max_row_drift': max(rows)})
    return {'entry_offset': entry, 'points': points,
            'max_row_drift': max(point['max_row_drift'] for point in points)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT/'results/rigid_oscillatory_checked_e02')
    parser.add_argument('--endpoint-cache', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    total = perf_counter()
    mp.dps = 130
    source = ROOT/'results/rigid_stokes_e02/results.json'
    previous = json.loads(source.read_text())
    if previous['status'] != 'complete':
        raise ValueError('The first-pulse calculation must be complete')
    for name in ('compare_rigid_oscillatory.py', 'rigid_monodromy.py', 'compare_rigid_monodromy.py',
                 'compare_pii.py', 'pii_core.py', 'high_precision.py', 'rk45_multiprecision.py',
                 'test_rigid_oscillatory.py'):
        shutil.copy2(ROOT/name, args.output/name)
    hashes = dict(previous['protected_hashes'])
    hashes[str(source)] = hashlib.sha256(source.read_bytes()).hexdigest()
    data = {'status': 'running', 'epsilon': '.2', 'interval': [-7, 8],
            'comparison_digits': 90, 'protected_hashes': hashes, 'monitor': {}, 'rk_trials': {}}

    def save():
        (args.output/'results.json').write_text(json.dumps(encode(data), indent=2)+'\n')

    print('Background and extrema on [-7,8]', flush=True)
    ref = r.Reference(end='8')
    peaks = maxima(ref)
    finer_peaks = maxima(ref, '.005')
    if len(peaks) != len(finer_peaks) or len(peaks) < 17:
        raise ValueError('Unresolved extrema or insufficient oscillations')
    data['peak_location_refinement'] = max(abs(a['t']-b['t']) for a, b in zip(peaks, finer_peaks))
    regular_index = next(j for j, p in enumerate(peaks)
                         if p.get('relative_period_change', mp.inf) < mp.mpf('.05')
                         and p.get('relative_height_change', mp.inf) < mp.mpf('.05'))
    entry = float(peaks[regular_index]['t']-ref.t0)
    new_times = [peaks[j]['t'] for j in (4, regular_index, 12, 16)]
    new_times += [(peaks[15]['t']+peaks[16]['t'])/2, ref.end]
    offsets = sorted(set(previous['offsets']+[float(t-ref.t0) for t in new_times]))
    data.update(peaks=peaks, regular_peak_number=regular_index+1,
                regular_entry_offset=entry, offsets=offsets,
                regularity_threshold='.05', t_star=previous['t_star'])
    coarse = r.Reference(end='8', digits=65, tolerance='1e-27', order=32)
    data['reference'] = {'F': {s: ref.matrix(ref.t0+mp.mpf(s)) for s in offsets},
                         'state': {s: ref.at(ref.t0+mp.mpf(s)) for s in offsets},
                         'steps': len(ref.segments),
                         'refinement_error': max(relative(coarse.matrix(ref.t0+mp.mpf(s)),
                                                          ref.matrix(ref.t0+mp.mpf(s))) for s in offsets)}
    jac = {}
    for offset in previous['offsets']:
        if relative(decode(previous['reference']['F'][str(offset)]),
                    ref.matrix(ref.t0+mp.mpf(offset))) > 1e-35:
            raise ValueError('The old background and the continuation disagree')
        record = previous['monitor'][str(offset)]
        data['monitor'][offset] = record
        jac[offset] = decode(record['J'])
    data['reused_monitor_offsets'] = previous['offsets']
    settings = dict(radius=8, formal_order=160, tolerance='1e-48', order=48, vertex='1.5')
    data['monitor_settings'] = {**settings, 'digits': 130}
    refined_origin = decode(previous['monitor_refinements']['0.0']['J'])
    cache = None
    if args.endpoint_cache:
        cache = json.loads(args.endpoint_cache.read_text())
        if cache['monitor_settings'] != data['monitor_settings']:
            raise ValueError('Cached endpoint used different monitor settings')
        if relative(decode(cache['reference_F']), ref.matrix(ref.end)) > 1e-35:
            raise ValueError('Cached endpoint used a different background')
        hashes[str(args.endpoint_cache.resolve())] = hashlib.sha256(args.endpoint_cache.read_bytes()).hexdigest()
        shutil.copy2(args.endpoint_cache, args.output/'endpoint_cache.json')
        data['monitor'][offsets[-1]] = cache['monitor']
        jac[offsets[-1]] = decode(cache['monitor']['J'])
        data['reused_endpoint'] = True
    print('Peaks:', len(peaks), '; regular entry:', float(ref.t0+entry), flush=True)
    # Check the far endpoint before investing in all intermediate points.
    for offset in [offsets[-1]]+[s for s in offsets if s not in jac and s != offsets[-1]]:
        if offset in jac:
            continue
        t = ref.t0+mp.mpf(offset)
        print('Independent Stokes monitor at t=', mp.nstr(t, 12), flush=True)
        s, j, diagnostic = r.monodromy(ref, t, **settings)
        jac[offset] = j
        rows = row_relative(j*ref.matrix(t), jac[0.])
        data['monitor'][offset] = {'s': s, 'J': j, 'diagnostic': diagnostic,
                                   'row_reference_variation_drift': rows,
                                   'row_refined_origin_drift': row_relative(j*ref.matrix(t), refined_origin)}
        print('  reference drift:', max(rows), flush=True)
        save()
        if max(rows) > 1e-18:
            data['status'] = 'failed_monitor_resolution'
            save()
            raise RuntimeError('Spectral monitor needs refinement before comparison')
    if args.endpoint_cache and args.endpoint_cache.with_name('endpoint_refined.json').exists():
        check_path = args.endpoint_cache.with_name('endpoint_refined.json')
        check = json.loads(check_path.read_text())
        data['endpoint_tolerance_refinement'] = {
            'coarser_settings': check['settings'],
            'coarser_row_drift': check['row_reference_variation_drift'],
            'change_of_J_rows': row_relative(jac[offsets[-1]], decode(check['J']))}
        shutil.copy2(check_path, args.output/'endpoint_coarser_monitor.json')
    ref_values = {s: ref.matrix(ref.t0+mp.mpf(s)) for s in offsets}
    data['reference_monitor'] = metrics(ref_values, ref, offsets, jac)
    data['reference_post_drift'] = post_drift(ref_values, jac, offsets, entry)
    base_s = decode(previous['monitor']['0.0']['s'])
    data['stokes_drift_by_row'] = [max(row_relative(decode(v['s']) if isinstance(v['s'], list)
                                                   else v['s'], base_s)[j]
                                      for v in data['monitor'].values()) for j in range(4)]
    save()

    def trial(tolerance):
        key = mp.nstr(mp.mpf(tolerance), 14)
        if key in data['rk_trials']:
            return key
        print('RK tolerance', key, flush=True)
        with mp.workdps(90):
            start = perf_counter()
            def rhs(s, y):
                potential = ref.potential(ref.t0+s)
                e = ref.epsilon
                return [y[1]/e, -potential*y[0]/e, y[3]/e, -potential*y[2]/e]
            states, stats = rk.integrate(rhs, offsets, list(map(mp.mpf, [1, 0, 0, 1])), key)
            values = {s: mp.matrix([[y[0], y[2]], [y[1], y[3]]]) for s, y in states.items()}
            data['rk_trials'][key] = {**metrics(values, ref, offsets, jac),
                                      'post_drift': post_drift(values, jac, offsets, entry),
                                      'F': values, 'seconds': perf_counter()-start, **stats}
        print('  E, D, post:', *(data['rk_trials'][key][field] for field in
                                ('max_solution_error', 'max_row_variation_drift')),
              data['rk_trials'][key]['post_drift']['max_row_drift'], flush=True)
        save()
        return key

    trial('1e-12')
    trial(previous['pairs']['1e-14']['rk_tolerance'])
    print('Contour continuation; initial tolerance 1e-14, new points 1e-34', flush=True)
    old_contour = previous['contours']['1e-14']
    with mp.workdps(90):
        start = perf_counter()
        method = r.Contours(ref, radius=8, formal_order=80, tolerance='1e-14', order=40, vertex='1.5')
        mismatch = relative(method.initial, decode(old_contour['raw_initial_F']))
        if mismatch > 1e-65:
            raise ValueError('The fixed initial contour basis changed')
        method.settings.update(tolerance='1e-34', order=48)
        values = {float(k): decode(v) for k, v in old_contour['F'].items()}
        diagnostics = {float(k): v for k, v in old_contour['diagnostics'].items()}
        if cache:
            cached = cache['contour']
            if cached['settings'] != method.settings or relative(decode(cached['raw_initial_F']), method.initial) > 1e-65:
                raise ValueError('Cached contour settings or initial basis differ')
            values[offsets[-1]] = decode(cached['F'])
            diagnostics[offsets[-1]] = cached['diagnostics']
        for offset in offsets:
            if offset in values:
                continue
            t = ref.t0+mp.mpf(offset)
            print('  contour t=', mp.nstr(t, 12), flush=True)
            values[offset], diagnostics[offset] = method.at(t)
        data['contour'] = {**metrics(values, ref, offsets, jac),
                            'post_drift': post_drift(values, jac, offsets, entry),
                            'F': values, 'diagnostics': diagnostics,
                            'initial_tolerance': '1e-14', 'new_point_tolerance': '1e-34',
                            'new_point_order': 48,
                            'seconds_new_work': perf_counter()-start,
                            'reused_offsets': previous['offsets'],
                            'initial_basis_mismatch': mismatch, 'raw_initial_F': method.initial,
                            'weights': method.weights}
    target = mp.mpf(data['contour']['max_solution_error'])
    print('Contour E, D, post:', target, data['contour']['max_row_variation_drift'],
          data['contour']['post_drift']['max_row_drift'], flush=True)
    for _ in range(6):
        best = min(data['rk_trials'], key=lambda k: abs(mp.log(mp.mpf(data['rk_trials'][k]['max_solution_error'])/target)))
        ratio = mp.mpf(data['rk_trials'][best]['max_solution_error'])/target
        if 1/mp.mpf('1.1') <= ratio <= mp.mpf('1.1'):
            break
        trial(mp.mpf(best)/ratio)
    best = min(data['rk_trials'], key=lambda k: abs(mp.log(mp.mpf(data['rk_trials'][k]['max_solution_error'])/target)))
    ratio = data['rk_trials'][best]['max_solution_error']/float(target)
    data['matched_pair'] = {'rk_tolerance': best, 'error_ratio_RK_over_contour': ratio,
                            'matched': 1/1.1 <= ratio <= 1.1}
    data['protected_unchanged'] = all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in hashes.items())
    data['seconds'] = perf_counter()-total
    data['status'] = 'complete'
    save()
    print(json.dumps({'matched_pair': data['matched_pair'], 'seconds': data['seconds'],
                       'protected_unchanged': data['protected_unchanged']}, indent=2), flush=True)


if __name__ == '__main__':
    main()
