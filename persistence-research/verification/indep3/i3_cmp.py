import json, sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i3_enum import *
B = '../glm/L2b/'
for T in TARGETS:
    mine = configs(T); sj = json.load(open(B + f'solve_t{T}.json')); theirs = {}
    for ms in sj['multisets']:
        for cf in ms['configs']:
            key = (cf['S_low'], tuple(cf['far'])); assert key not in theirs; theirs[key] = dict(cf, multiset=tuple(ms['multiset']))
    print(T, 'only_mine', sorted(set(mine)-set(theirs)), 'only_theirs', sorted(set(theirs)-set(mine)),
          'msmis', [k for k in mine if k in theirs and tuple(mine[k]['multiset']) != theirs[k]['multiset']])
    for k in mine:
        if k not in theirs: continue
        td = theirs[k]['status'] == 'parity-dead'
        if td != mine[k]['dead_weak']: print('   DEAD MISMATCH', k, mine[k]['multiset'], 'mine dead', mine[k]['dead_weak'], 'B', theirs[k]['status'], theirs[k].get('slices'), (111 + k[0]) % 40)
    print('   B status', dict(collections.Counter(v['status'].split(' (')[0] for v in theirs.values())), 'open', sj['open'] if len(str(sj['open']))<300 else len(sj['open']))
