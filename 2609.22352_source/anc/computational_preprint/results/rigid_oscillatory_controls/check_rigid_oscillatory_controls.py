"""Controls for accuracy allocation and spectral conditioning after the pulse."""
import hashlib
import json
from pathlib import Path
from time import perf_counter

from mpmath import mp

from compare_pii import encode, relative
from compare_rigid_monodromy import metrics
from compare_rigid_oscillatory import decode, post_drift
import rigid_monodromy as r
import rk45_multiprecision as rk


ROOT = Path(__file__).resolve().parent


def main():
    source = ROOT/'results/rigid_oscillatory_checked_e02/results.json'
    original_bytes = source.read_bytes()
    data = json.loads(original_bytes)
    output = ROOT/'results/rigid_oscillatory_controls'
    output.mkdir(exist_ok=False)
    mp.dps = 90
    ref = r.Reference(end='8')
    offsets = data['offsets']
    entry = data['regular_entry_offset']
    jac = {float(k): decode(v['J']) for k, v in data['monitor'].items()}
    result = {'source_sha256': hashlib.sha256(original_bytes).hexdigest(),
              'status': 'running', 'comparison_digits': 90}

    def save():
        (output/'results.json').write_text(json.dumps(encode(result), indent=2)+'\n')

    print('RK: preserve the state at t=-1 and tighten tolerance to 1e-16', flush=True)
    early = data['rk_trials']['5.399977346781e-14']
    values = {float(s): decode(f) for s, f in early['F'].items() if float(s) <= 6}
    y = values[6.]
    initial = [y[0, 0], y[1, 0], y[0, 1], y[1, 1]]
    local_offsets = [0.]+[s-6 for s in offsets if s > 6]
    if any(mp.mpf(s-6)-1 != mp.mpf(s)-7 for s in offsets if s > 6):
        raise ValueError('Local time shift changed output times')

    def rhs(s, y):
        k, e = ref.potential(s-1), ref.epsilon
        return [y[1]/e, -k*y[0]/e, y[3]/e, -k*y[2]/e]

    start = perf_counter()
    states, stats = rk.integrate(rhs, local_offsets, initial, '1e-16')
    for s in offsets:
        if s > 6:
            y = states[s-6]
            values[s] = mp.matrix([[y[0], y[2]], [y[1], y[3]]])
    result['rk_tightened'] = {**metrics(values, ref, offsets, jac),
                              'post_drift': post_drift(values, jac, offsets, entry),
                              'F': values, 'early_tolerance': '5.399977346781e-14',
                              'late_tolerance': '1e-16', 'switch_t': -1,
                              'seconds_new': perf_counter()-start, **stats}
    print('RK tightened E, Dosc:', result['rk_tightened']['max_solution_error'],
          result['rk_tightened']['post_drift']['max_row_drift'], flush=True)
    save()

    print('Contour endpoint: preserve the initial basis, tighten tolerance to 1e-40', flush=True)
    method = r.Contours(ref, radius=8, formal_order=80, tolerance='1e-14', order=40, vertex='1.5')
    if relative(method.initial, decode(data['contour']['raw_initial_F'])) > 1e-65:
        raise ValueError('Initial contour basis changed')
    method.settings.update(tolerance='1e-40', order=48)
    start = perf_counter()
    f, diagnostic = method.at(ref.end)
    c_entry = decode(data['contour']['F'][str(entry)])
    point_values = {entry: c_entry, 15.: f}
    result['contour_endpoint_refined'] = {
        'F': f, 'diagnostics': diagnostic, 'tolerance': '1e-40',
        'solution_error': relative(f, ref.matrix(ref.end)),
        'post_drift': post_drift(point_values, jac, [entry, 15.], entry),
        'change_of_F': relative(f, decode(data['contour']['F']['15.0'])),
        'seconds_new': perf_counter()-start}
    print('Contour endpoint E, Dosc:', result['contour_endpoint_refined']['solution_error'],
          result['contour_endpoint_refined']['post_drift']['max_row_drift'], flush=True)
    result['source_unchanged'] = source.read_bytes() == original_bytes
    result['status'] = 'complete'
    (output/'check_rigid_oscillatory_controls.py').write_bytes(Path(__file__).read_bytes())
    save()


if __name__ == '__main__':
    main()
