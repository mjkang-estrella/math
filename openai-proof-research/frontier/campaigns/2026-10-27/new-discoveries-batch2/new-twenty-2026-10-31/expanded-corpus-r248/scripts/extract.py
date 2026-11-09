"""Extract the 20 reserved MathDB records with exact raw lines and hashes (adapted from r245/scripts/extract.py).
Writes raw/<id>.jsonl, extracted.json (refuses to overwrite extracted.json). Pure python, no subprocess."""
import pathlib, json, hashlib, sys
D = pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248')
B = D.parent.parent
sha = lambda b: hashlib.sha256(b).hexdigest()
r = json.loads((D / 'reservation.json').read_text())
ids = set(r['ids'])
out = {}
if (D / 'extracted.json').exists():
    raise SystemExit('extracted.json exists; refusing to overwrite')
(D / 'raw').mkdir(exist_ok=True)
for p in sorted((B / 'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
    data = p.read_bytes()
    ch = sha(data)
    for n, line in enumerate(data.splitlines(keepends=True), 1):
        o = json.loads(line)
        i = o['mathdb_id']
        if i not in ids:
            continue
        (D / f'raw/{i}.jsonl').write_bytes(line)
        out[str(i)] = {'mathdb_id': i, 'title': o['title'], 'statement': o['statement'], 'source_url': o['source_url'],
                       'other_fields': {k: v for k, v in o.items() if k not in ('statement',)},
                       'provenance': {'chunk': str(p), 'line_1based': n, 'chunk_sha256': ch, 'raw_sha256': sha(line),
                                      'statement_utf8_sha256': sha(o['statement'].encode())}}
assert len(out) == 20, len(out)
(D / 'extracted.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
for i, o in sorted(out.items()):
    print(i, o['title'], '\n', o['statement'], '\nSOURCE', o['source_url'], '\n')
