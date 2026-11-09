# Assemble results.json (exactly 20 ID-keyed entries) from extracted.json provenance and the
# dispositions recorded below.  Run with python3 -I from any directory.
import json, pathlib, hashlib
D = pathlib.Path(__file__).resolve().parents[1]
ext = json.loads((D / 'extracted.json').read_text())
res = json.loads((D / 'scripts' / 'dispositions.json').read_text())
assert sorted(ext) == sorted(res), (sorted(set(ext) ^ set(res)))
out = {}
for k in sorted(ext):
    e = ext[k]; r = res[k]
    raw = (D / 'raw' / f'{k}.jsonl').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == e['provenance']['raw_sha256']
    out[k] = {'mathdb_id': int(k), 'title': e['title'], 'source_url': e['source_url'],
              'literal_statement': e['statement'], 'provenance': e['provenance'], **r}
assert len(out) == 20
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(out), 'entries')
