# Builds results.json (exactly 20 ID-keyed entries) from extracted.json provenance and the dispositions below.
import json, pathlib, sys
D = pathlib.Path(sys.argv[1])
ex = json.loads((D / 'extracted.json').read_text())
res = json.loads((D / 'scripts' / 'dispositions.json').read_text())
ids = json.loads((D / 'reservation.json').read_text())['ids']
assert sorted(map(str, ids)) == sorted(res.keys()), (sorted(map(str, ids)), sorted(res.keys()))
out = {}
for i in map(str, ids):
    o = ex[i]
    out[i] = {
        'mathdb_id': int(i),
        'title': o['title'],
        'source_url': o.get('source_url'),
        'provenance': o['provenance'],
        **res[i],
    }
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print(len(out), 'entries')
