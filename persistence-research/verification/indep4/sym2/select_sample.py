# stratified random sample of sym2 certificates (scope=full), strata = (dim, kill-dependency set).  python3 -I sym2/select_sample.py seed
import json, random, collections, sys
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 7
rnd = random.Random(seed)
k = json.load(open('../highdim/sym2/kill_usage.json'))
def v2(n):
    c = 0
    while n % 2 == 0: n //= 2; c += 1
    return c
strata = collections.defaultdict(list)
for f, v in k.items():
    m = v['meta']
    if m['scope'] != 'full': continue
    strata[(m['dim'], tuple(sorted(v['dependencies'])))].append(f)
sel = {}
for key, fs in sorted(strata.items()):
    n = min(len(fs), 9)
    for f in rnd.sample(fs, n): sel[f] = 'stratum'
# extra: sumset-dependent (1415 certs) and mod8 + large t0, tail-only
sums = [f for f, v in k.items() if 'unaligned_sumset' in v['dependencies'] and v['meta']['scope'] == 'full' and f not in sel]
for f in rnd.sample(sums, 80): sel[f] = 'extra-sumset'
bigt = [f for f, v in k.items() if v2(v['meta']['K']) >= 10 and v['meta']['scope'] == 'full' and f not in sel]
for f in rnd.sample(bigt, 60): sel[f] = 'extra-t0>=10'
dim1 = [f for f, v in k.items() if v['meta']['dim'] == 1 and v['meta']['scope'] == 'full' and f not in sel]
for f in rnd.sample(dim1, 40): sel[f] = 'extra-dim1'
stage = collections.defaultdict(list)
for f, v in k.items():
    if v['meta']['scope'] == 'full' and f not in sel: stage[v['meta']['extra'].get('stage')].append(f)
for s, fs in stage.items():
    for f in rnd.sample(fs, min(len(fs), 25)): sel[f] = 'extra-stage-' + str(s)
json.dump(sel, open('sym2/sample_%d.json' % seed, 'w'), indent=0)
c = collections.Counter(sel.values()); print(len(sel), dict(c), 'strata', len(strata))
dims = collections.Counter(k[f]['meta']['dim'] for f in sel); print('dims', sorted(dims.items()))
dep = collections.Counter(d for f in sel for d in k[f]['dependencies']); print(dict(dep))
