import json, glob, collections
rows = [json.load(open(f)) for f in sorted(glob.glob('logs/all/*.json'))]
tot = collections.Counter(); kinds = collections.Counter(); uk = collections.Counter(); byk = collections.defaultdict(lambda: collections.Counter())
dims = collections.Counter(); nodes = 0
for r in rows:
    dims[(r['dim'], r['result'])] += 1
    for k, v in r['stats'].items(): tot[k] += v
    for k, v in r['kinds'].items(): kinds[k] += v
    for k, v in r['ukinds'].items(): uk[k] += v
    stage = r['file'].split('/')[-2]
    byk[stage]['certs'] += 1; byk[stage][r['result']] += 1
    for k, v in r['kinds'].items(): byk[stage][k] += v
    byk[stage]['refinements'] += r['stats']['refinements']
    byk[stage]['sumset_cert'] += any(x.startswith('sumset') for x in r['ukinds'])
    byk[stage]['sz_leaves'] += r['stats'].get('leaf_sz_ok', 0)
    byk[stage]['prime_leaves'] += r['stats'].get('leaf_prime_ok', 0)
nodes = sum(sum(1 for _ in open(r['file'])) - 1 for r in rows)
out = dict(certs=len(rows), results=dict(collections.Counter(r['result'] for r in rows)), dims={str(k): v for k, v in dims.items()},
           totals=dict(tot), kill_instances=dict(kinds), unique_kills=dict(uk), nodes=nodes, by_stage={k: dict(v) for k, v in byk.items()},
           claimed_solutions=sum(len(r['claimed']) for r in rows), brute_hits=sum(len(r['brute']) for r in rows))
json.dump(out, open('summary_F.json', 'w'), indent=1)
print(json.dumps(out, indent=1))
