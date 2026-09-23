"""A posteriori refinement decision in normalized monodromy units."""
from mpmath import mp


def assess(increments, target, contraction_limit='0.5'):
    target = mp.mpf(target)
    limit = mp.mpf(contraction_limit)
    keys = ('contour_increment', 'reference_increment', 'monitor_increment',
            'reference_conservation_defect', 'previous_contour_increment')
    values = {key: mp.mpf(increments[key]) for key in keys}
    if not mp.isfinite(target) or target <= 0 or not 0 < limit < 1:
        raise ValueError('Positive finite target and contraction limit in (0,1) required')
    if any(not mp.isfinite(v) or v < 0 for v in values.values()):
        raise ValueError('Increments must be finite and nonnegative')
    previous = values['previous_contour_increment']
    contraction = values['contour_increment']/previous if previous else mp.inf
    # Reserve the fifth share for the separate radius/formal-order check.
    failed = [key for key in keys[:4] if values[key] > target/5]
    if contraction > limit:
        failed.append('contraction')
    return {'accepted': not failed, 'failed_checks': failed, 'target': target,
            'contraction': contraction, 'contraction_limit': limit,
            'observed_sum': sum(values[k] for k in keys[:4]),
            'interpretation': 'Observed refinement criterion; not a certified error bound.'}
