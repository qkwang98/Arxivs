# Changelog (reverse chronological):
# 2026-08-01 - Claude: simplified now that both sides write JSON with the same f_vector
#   convention (parameter_space_n5d1.jl pads Oscar's f_vector to match Sage's) -- no longer needs
#   to know about the Sage-vs-Oscar trivial-entry discrepancy, both files load identically.
# 2026-08-01 - Claude: created this file. Diffs parameter_space_n5d1.py's Sage output against
#   parameter_space_n5d1.jl's Julia/Oscar output for the same shared point list, matching Jan's
#   requirement that every n=5,d=1 experiment run in tandem across both installs.

"""
Compares a Sage results JSON (parameter_space_n5d1.py's run_on_points output) against a Julia
results JSON (parameter_space_n5d1.jl's run_on_points output) for the same underlying point list.
Matches points by their a-vector and reports any f-vector mismatch -- treated as a stop-the-line
bug, not a footnote, per this exploration's tandem-verification requirement.

    python3 compare_n5d1_tandem.py <sage_results.json> <julia_results.json>
"""

import json
import sys


def load(path):
    with open(path) as f:
        data = json.load(f)
    return {tuple(entry['a']): tuple(entry['f_vector']) for entry in data['points']}


def main(sage_path, julia_path):
    sage_results = load(sage_path)
    julia_results = load(julia_path)

    if set(sage_results) != set(julia_results):
        only_sage = set(sage_results) - set(julia_results)
        only_julia = set(julia_results) - set(sage_results)
        print(f'MISMATCHED POINT SETS: {len(only_sage)} only in Sage, '
              f'{len(only_julia)} only in Julia')
        if only_sage:
            print('  only in Sage:', sorted(only_sage)[:5], '...')
        if only_julia:
            print('  only in Julia:', sorted(only_julia)[:5], '...')

    mismatches = []
    for a in sorted(set(sage_results) & set(julia_results)):
        if sage_results[a] != julia_results[a]:
            mismatches.append((a, sage_results[a], julia_results[a]))

    n_common = len(set(sage_results) & set(julia_results))
    if mismatches:
        print(f'FOUND {len(mismatches)}/{n_common} F-VECTOR MISMATCHES:')
        for a, fv_sage, fv_julia in mismatches[:20]:
            print(f'  a={a}: sage={fv_sage} julia={fv_julia}')
        if len(mismatches) > 20:
            print(f'  ... and {len(mismatches) - 20} more')
        sys.exit(1)
    else:
        print(f'OK: all {n_common} points agree between Sage and Julia/Oscar.')


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(1)
    main(sys.argv[1], sys.argv[2])
