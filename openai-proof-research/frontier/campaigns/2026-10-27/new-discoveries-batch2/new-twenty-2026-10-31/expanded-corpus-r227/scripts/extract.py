import pathlib, json, hashlib, sys
# Usage: extract.py LANE_DIR  (lane directory passed explicitly; no __file__ use)
D = pathlib.Path(sys.argv[1]).resolve()
B = D.parent.parent  # new-discoveries-batch2
sha = lambda b: hashlib.sha256(b).hexdigest()
r = json.loads((D / 'reservation.json').read_text())
ids = set(r['ids'])
out = {}
man = B / 'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json'
for p in sorted((B / 'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
    data = p.read_bytes(); ch = sha(data)
    for n, line in enumerate(data.splitlines(keepends=True), 1):
        o = json.loads(line); i = o['mathdb_id']
        if i not in ids:
            continue
        rp = D / f'raw/{i}.jsonl'
        if rp.exists():
            assert rp.read_bytes() == line
        else:
            rp.write_bytes(line)
        out[str(i)] = {'mathdb_id': i, 'title': o['title'], 'statement': o['statement'],
                       'source_url': o.get('source_url'), 'keys': sorted(o.keys()),
                       'provenance': {'chunk': str(p), 'line_1based': n, 'chunk_sha256': ch,
                                      'raw_sha256': sha(line), 'raw_includes_newline': line.endswith(b'\n'),
                                      'statement_utf8_sha256': sha(o['statement'].encode())}}
assert len(out) == 20, len(out)
out['_manifest_sha256'] = sha(man.read_bytes())
(D / 'extracted.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
for i, o in out.items():
    if i.startswith('_'):
        continue
    print('=====', i, o['title'], '\nSOURCE', o['source_url'], '\n', o['statement'], '\n')
