#!/usr/bin/env python3
"""Monochrome diagnostic for the rigid-loss PII background and tangent gain."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent


def main():
    data = json.loads((ROOT/'results/rigid_pii_verified/results.json').read_text())
    if data['status'] != 'complete':
        raise ValueError('Incomplete pilot')
    plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,axes = plt.subplots(1,2,figsize=(11,4.4),layout='constrained')
    theta = np.linspace(-2,2,401)
    a = data['a_star']
    axes[0].plot(theta,a-4*a/(1+4*a*a*theta*theta),color='black',linewidth=1.8,label='Limiting pulse')
    styles = {'.05':':','.02':'--','.005':'-.'}
    for key,style in styles.items():
        run = next(v for v in data['runs'] if v['epsilon']==float(key))
        axes[0].plot(run['offsets'],run['u'],color='black',linestyle=style,linewidth=1,
                     label=f'epsilon = {key}')
    axes[0].set(xlabel=r'$(t-t_{\rm peak})/\epsilon$',ylabel='u',title='First pulse: smooth PII background')
    axes[0].legend(frameon=False,fontsize=9)
    eps = np.array([v['epsilon'] for v in data['runs']])
    gain = np.array([v['max_gain_balanced_input'] for v in data['runs']])
    axes[1].loglog(eps,gain,'o-',color='black',markerfacecolor='white',label='Tangent calculation')
    constant = gain[-1]*eps[-1]**.7
    axes[1].loglog(eps,constant*eps**(-.7),'--',color='black',label=r'$C\epsilon^{-7/10}$')
    axes[1].set(xlabel=r'$\epsilon$',ylabel='Maximum singular value, balanced input',
                title='Amplification near the first pulse')
    axes[1].legend(frameon=False,fontsize=9)
    axes[1].grid(True,which='major',color='.85',linewidth=.5)
    output = ROOT/'results/rigid_pii_amplification.png'
    fig.savefig(output,dpi=180)
    plt.close(fig)
    print(output)


if __name__ == '__main__':
    main()
