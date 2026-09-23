"""Generate parameter-study tables and decisions from completed records."""
import argparse
import hashlib
import json
from pathlib import Path

from mpmath import mp

from accuracy_budget import assess
from compare_pii import encode
from parameter_study import CASES


ROOT = Path(__file__).resolve().parent


def sci(v):
    a,b = f'{float(v):.3e}'.split('e')
    return rf'${a}\cdot10^{{{int(b)}}}$'


def main():
    mp.dps = 70
    parser = argparse.ArgumentParser()
    parser.add_argument('--input',type=Path,default=ROOT/'results/parameter_study')
    parser.add_argument('--tables',type=Path,default=ROOT/'manuscript_ru/tables')
    args = parser.parse_args()
    rows, budget_rows, summary = [], [], {}
    for name,(kind,a,b) in CASES.items():
        path = args.input/name/'results.json'
        d = json.loads(path.read_text())
        if d['status'] != 'complete':
            raise ValueError('Unresolved case '+name)
        trunc = json.loads(path.with_name('truncation_check.json').read_text())
        if hashlib.sha256(path.read_bytes()).hexdigest() != trunc['source_sha256']:
            raise ValueError('Stale truncation check '+name)
        label = (rf'$q_0={a},\ w_0={b}$' if kind == 'PII' else rf'$\theta_0={a}+{b}\ii$')
        c = d['contours'][1]
        r = d['rk_trials'][d['pair']['rk_tolerance']]
        rows.append(label+' & '+
                    ' & '.join(sci(v) for v in (c['E'],r['E'],c['D'],r['D']))+
                    f" & {float(d['pair']['D_ratio']):.3f}"+r'\\')
        check = assess(d['refinement'],'1e-9')
        check['truncation_increment'] = trunc['increment']
        check['truncation_resolved'] = bool(mp.mpf(trunc['increment']) <= mp.mpf('1e-9')/5)
        check['observed_sum'] += mp.mpf(trunc['increment'])
        check['combined_accepted'] = check['accepted'] and check['truncation_resolved']
        if not check['combined_accepted']:
            raise ValueError('Target budget failed: '+name+' '+str(check))
        check['actual_fine_drift'] = d['contours'][2]['D']
        check['target_verified'] = bool(mp.mpf(check['actual_fine_drift']) <= check['target'])
        if not check['target_verified']:
            raise ValueError('Independent drift exceeds target: '+name)
        floor = max(mp.mpf(d['refinement'][k]) for k in
                    ('reference_increment','monitor_increment','reference_conservation_defect'))
        budget_rows.append(label+' & '+' & '.join(sci(v) for v in
            (d['refinement']['contour_increment'],floor,trunc['increment'],check['actual_fine_drift']))+r'\\')
        summary[name] = check
    args.tables.mkdir(parents=True,exist_ok=True)
    for filename,spec,head,body in [
        ('parameters.tex','lrrrrr',r'Данные & $E_C$ & $E_{\rm RK}$ & $D_C$ & $D_{\rm RK}$ & $D_{\rm RK}/D_C$',rows),
        ('budget.tex','lrrrr',r'Данные & $c_2$ & $\max(r,j,d_R)$ & Уточнение $R,N$ & $D_C^{(2)}$',budget_rows)]:
        (args.tables/filename).write_text('\\begin{tabular}{'+spec+'}\n\\toprule\n'+head+r'\\'+
            '\n\\midrule\n'+'\n'.join(body)+'\n\\bottomrule\n\\end{tabular}\n')
    (args.input/'decisions.json').write_text(json.dumps(encode(summary),indent=2)+'\n')
    print(json.dumps(encode(summary),indent=2))


if __name__ == '__main__':
    main()
