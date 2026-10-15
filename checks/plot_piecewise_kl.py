#!/usr/bin/env python3
"""Plot the frozen tail comparison without recomputing any probabilities."""

import csv
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
with (root/'checks/results/piecewise_kl_matrix.csv').open() as handle:
    rows = [r for r in csv.DictReader(handle)
            if (int(r['N']),int(r['k']),int(r['m'])) == (101,50,17)
            and r['v'].endswith('.0')]
fig, axes = plt.subplots(1,2,figsize=(10,3.8),layout='constrained')
curves = [
 ('exact_log_tail','Exact probability','#111111','-'),
 ('optimized_factorial_log_bound','Optimized factorial','#d1495b','--'),
 ('piecewise_kl_log_bound','Piecewise KL','#147d64','-'),
 ('scaled_kl_log_bound','Scaled KL','#3266a8','--'),
 ('four_binomial_kl_best_log_bound','Best binomial KL','#b17b19',':')]
for ax, side in zip(axes,['lower','upper']):
    part = sorted((r for r in rows if r['side']==side),key=lambda r:float(r['v']))
    for key,label,color,style in curves:
        ax.plot([float(r['v']) for r in part],[-float(r[key]) for r in part],
                label=label,color=color,linestyle=style,linewidth=1.5)
    ax.set(xlabel='Integer threshold',ylabel='Negative log probability or bound',title=f'{side.capitalize()} tail')
    ax.grid(alpha=.2)
    ax.spines[['top','right']].set_visible(False)
axes[0].legend(frameon=False,fontsize=8)
fig.suptitle('Hypergeometric N = 101, k = 50, m = 17',fontsize=12)
for suffix in ['pdf','png']:
    fig.savefig(root/f'research/tail_bounds/tail_comparison.{suffix}',dpi=180)
print('PASS: plotted frozen exact and bound columns')
