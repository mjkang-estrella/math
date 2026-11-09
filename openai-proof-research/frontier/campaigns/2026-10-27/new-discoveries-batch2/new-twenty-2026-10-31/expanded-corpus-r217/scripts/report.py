import sys, json, pathlib, hashlib
D = pathlib.Path(sys.argv[1]).resolve()
ext = json.loads((D / 'extracted.json').read_text())
dis = json.loads((D / 'scripts/dispositions.json').read_text())
res = json.loads((D / 'reservation.json').read_text())
assert set(map(str, res['ids'])) == set(ext) == set(dis), 'id mismatch'
out = {}
for i in map(str, res['ids']):
    e = ext[i]; d = dis[i]
    raw = (D / f'raw/{i}.jsonl').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == e['provenance']['raw_sha256']
    out[i] = {'mathdb_id': int(i), 'title': e['title'], 'source_url': e['source_url'],
              'provenance': e['provenance'], 'raw_line_file': f'raw/{i}.jsonl',
              'outcome': d['outcome'], 'review_depth': d['review_depth'], 'disposition': d['disposition'],
              'computation': d['computation'], 'candidate': False, 'lean_run': False}
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('entries', len(out))
