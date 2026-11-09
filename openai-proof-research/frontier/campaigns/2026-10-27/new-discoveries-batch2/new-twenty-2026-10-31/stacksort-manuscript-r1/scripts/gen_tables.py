#!/usr/bin/env python3
"""Generate the manuscript tables from the frozen exact P table (diagnostic data only).

Usage: python3 -I scripts/gen_tables.py <stack_pairs_P_1_82.json> <out_dir>
Writes table-small.md, table-large.md, table-facts.json.
"""
import json, math, sys
from decimal import Decimal, getcontext
from pathlib import Path

getcontext().prec = 80


def f(x, k=5):
    return f'{x:.{k}f}'


def main():
    P = {int(k): int(v) for k, v in json.load(open(sys.argv[1])).items()}
    out = Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)
    d = {n: Decimal(P[n]) / Decimal(math.factorial(n)) for n in P}
    root = {n: (d[n].ln() / n).exp() for n in P}
    ratio = {n: d[n] / d[n - 1] for n in P if n > 1}
    dbl = {n: ((d[n] / (4 * (n + 1))).ln() / (n + 1)).exp() for n in P}
    sup = {n: ((d[n] / ((n + 1) ** 2)).ln() / (n + 1)).exp() for n in P if n + 1 >= 8}
    small = ['| n | P_n | d_n^{1/n} | d_n / d_{n−1} |', '|---|---|---|---|']
    for n in range(1, 21):
        small.append(f'| {n} | {P[n]} | {f(root[n])} | {f(ratio[n]) if n > 1 else "–"} |')
    large = ['| n | P_n (leading digits) | d_n^{1/n} | d_n / d_{n−1} | β_n | σ_{n+1} |', '|---|---|---|---|---|---|']
    for n in (13, 20, 25, 30, 40, 49, 50, 60, 70, 78, 79, 80, 81, 82):
        s = str(P[n]); lead = f'{s[0]}.{s[1:5]} × 10^{{{len(s) - 1}}}'
        large.append(f'| {n} | {lead} | {f(root[n])} | {f(ratio[n])} | {f(dbl[n])} | {f(sup[n]) if n in sup else "–"} |')
    (out / 'table-small.md').write_text('\n'.join(small) + '\n')
    (out / 'table-large.md').write_text('\n'.join(large) + '\n')
    facts = {
        'root_strictly_increasing_2_to_82': all(root[n] > root[n - 1] for n in range(2, 83)),
        'ratio_strictly_decreasing_3_to_82': all(ratio[n] < ratio[n - 1] for n in range(3, 83)),
        'ratio_strictly_decreasing_from': min(m for m in range(3, 83) if all(ratio[n] < ratio[n - 1] for n in range(m, 83))),
        'root_82': float(root[82]), 'ratio_82': float(ratio[82]), 'beta_82': float(dbl[82]), 'beta_50': float(dbl[50]),
        'beta_49': float(dbl[49]), 'sigma_83': float(sup[82]), 'sigma_79': float(sup[78]), 'sigma_78': float(sup[77]),
        'P_50': str(P[50]), 'P_82': str(P[82]), 'P_82_digits': len(str(P[82])),
        'a10_source_check': float(((d[9] / 100).ln() / 10).exp()),
    }
    (out / 'table-facts.json').write_text(json.dumps(facts, indent=1) + '\n')
    print(json.dumps(facts, indent=1))


if __name__ == '__main__':
    main()
