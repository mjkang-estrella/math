import pathlib, json, hashlib, sys
# Lane directory passed explicitly (never derived under stdin).
D = pathlib.Path(sys.argv[1]).resolve()
B = D.parent.parent  # new-discoveries-batch2
sha = lambda b: hashlib.sha256(b).hexdigest()
r = json.loads((D / 'reservation.json').read_text())
ids = set(r['ids'])
out = {}
man = B / 'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for p in sorted(man.glob('mathdb-normalized-chunk-*.jsonl')):
    data = p.read_bytes()
    ch = sha(data)
    for n, line in enumerate(data.splitlines(keepends=True), 1):
        o = json.loads(line)
        i = o['mathdb_id']
        if i not in ids:
            continue
        rp = D / f'raw/{i}.jsonl'
        if not rp.exists():
            rp.write_bytes(line)
        assert rp.read_bytes() == line
        out[str(i)] = {'mathdb_id': i, 'title': o['title'], 'statement': o['statement'],
                       'source_url': o['source_url'],
                       'provenance': {'chunk': str(p), 'line_1based': n, 'chunk_sha256': ch,
                                      'raw_sha256': sha(line),
                                      'statement_utf8_sha256': sha(o['statement'].encode())}}
assert len(out) == 20, len(out)
ep = D / 'extracted.json'
ep.write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
for i, o in sorted(out.items()):
    print('=' * 8, i, o['title'], '\n', o['statement'], '\nSOURCE', o['source_url'])
