import json, random, collections, sys
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 3
rnd = random.Random(seed)
C = json.load(open('../highdim/sym2/summary.json'))['configurations']
closed = [k for k, v in C.items() if v['status'] == 'CLOSED']
by = collections.defaultdict(list)
for k in closed: by[(C[k]['coverage_method'], C[k]['dim'])].append(k)
for key, l in sorted(by.items()): print(key, len(l), 'domain_count median', sorted(C[k]['domain_count'] for k in l)[len(l)//2], 'max', max(C[k]['domain_count'] for k in l))
sel = []
quota = {'original_enlarged_cover': 24, 'distinct_fixed_positions': 22, 'position_partition': 16}
for m, q in quota.items():
    pool = [k for k in closed if C[k]['coverage_method'] == m]
    # stratify by dim inside method
    bd = collections.defaultdict(list)
    for k in pool: bd[C[k]['dim']].append(k)
    got = []
    dims = sorted(bd)
    i = 0
    while len(got) < min(q, len(pool)):
        d = dims[i % len(dims)]; i += 1
        cand = [k for k in bd[d] if k not in got]
        if cand: got.append(rnd.choice(cand))
    sel += got
tot = sum(C[k]['domain_count'] for k in sel)
print(len(sel), 'total domain certs', tot, collections.Counter((C[k]['coverage_method'], C[k]['dim']) for k in sel))
json.dump(sel, open('sym2/cfg_sample_%d.json' % seed, 'w'))
