# Merge n=12 shards for MathDB 345966 and compare the two quadruple histograms.
import json, pathlib, sys, collections, hashlib
D = pathlib.Path(sys.argv[1]); n = 12
shards = {'p': [(0,12),(12,24),(24,36),(36,48),(48,60),(60,72),(72,102),(102,132)],
          'i': [(0,40),(40,80),(80,120)]}
H = {}; counts = {}; files = {}
for kind, rs in shards.items():
    h = collections.Counter(); c = 0; cover = []
    for a, b in rs:
        f = D / 'outputs' / f'equidist-{n}-{kind}-{a}-{b}.json'
        data = f.read_bytes(); files[f.name] = hashlib.sha256(data).hexdigest()
        o = json.loads(data); assert o['n'] == n and o['kind'] == kind and o['prefix_range'] == [a, b]
        c += o['count']; cover.append((a, b))
        for *key, v in o['hist']: h[tuple(key)] += v
    total = 132 if kind == 'p' else 120
    assert sorted(cover)[0][0] == 0 and sorted(cover)[-1][1] == total and all(x[1] == y[0] for x, y in zip(sorted(cover), sorted(cover)[1:]))
    H[kind] = h; counts[kind] = c
bad = [(k, H['p'][k], H['i'][k]) for k in set(H['p']) | set(H['i']) if H['p'][k] != H['i'][k]]
print(json.dumps(dict(n=n, counts=counts, distinct_keys=[len(H['p']), len(H['i'])], bad_count=len(bad), bad_first=bad[:10],
                      histP_sha256=hashlib.sha256(repr(sorted(H['p'].items())).encode()).hexdigest(),
                      histI_sha256=hashlib.sha256(repr(sorted(H['i'].items())).encode()).hexdigest(), shard_sha256=files), indent=1))
