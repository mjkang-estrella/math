from research import *
records=json.loads((L/'provenance.json').read_text())
for rec in records:
 assert h(pathlib.Path(rec['copy']))==rec['sha256']
 if rec['kind']=='scientific frozen':assert h(pathlib.Path(rec['original']))==rec['sha256']
for rec in json.loads((L/'history-reused.json').read_text()):assert h(pathlib.Path(rec['path']))==rec['sha256']
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line);assert h(pathlib.Path(r['pdf']))==r['pdf_sha256'];assert h(pathlib.Path(r['text']))==r['text_sha256']
records.append(dict(kind='immutable source bindings',path='bindings.jsonl',sha256=h(L/'bindings.jsonl')))
records.append(dict(kind='immutable history reused in place',path='history-reused.json',sha256=h(L/'history-reused.json')))
records.append(dict(kind='limitations',wrong_body='sources/roy1997.pdf is de Shalit–Goren, not the cited Bernstein classes; use roy-correct.pdf',registry_head='unknown',counts='9 additional /39 total /next40; root only',resource_caps='AS/groupRSS512MiB CPU210 wall230; unchanged; RSS sampled',historical_registry_revision='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'))
(L/'provenance.json').write_text(json.dumps(records,indent=2))
excluded={'final-manifest.json','final-verification.json'}
manifest={str(p.relative_to(L)):dict(sha256=h(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
(L/'final-manifest.json').write_text(json.dumps(manifest,indent=2));print('Manifest entries',len(manifest))
