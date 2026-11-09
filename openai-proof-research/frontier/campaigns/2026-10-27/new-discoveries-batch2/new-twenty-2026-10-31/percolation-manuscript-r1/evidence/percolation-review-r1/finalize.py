import pathlib,json,hashlib
L=pathlib.Path.cwd()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
before=json.loads((L/'inputs-before.json').read_text());after={p:sha(pathlib.Path(p)) for p in before};assert before==after
(L/'inputs-after.json').write_text(json.dumps(after,indent=2))
r=json.loads((L/'mathdb-entry.json').read_text());p=pathlib.Path(r['provenance']['chunk']);raw=p.read_bytes().splitlines(keepends=True)[3157];(L/'mathdb-raw-line.json').write_bytes(raw);assert sha(p)==r['provenance']['chunk_sha256']
(L/'raw-input-receipt.json').write_text(json.dumps(dict(path=str(p),line=3158,chunk_before=sha(p),chunk_after=sha(p),raw_sha256=hashlib.sha256(raw).hexdigest(),declared_raw_sha256=r['provenance']['raw_sha256']),indent=2))
receipts={p.stem:json.loads(p.read_text()) for p in (L/'logs').glob('*.receipt.json')}
lean={k:v for k,v in receipts.items() if k.startswith(('lean-','checker-'))};assert len(lean)==68 and all(v['exit']==0 for v in lean.values())
summary=dict(lean_modules=34,leanchecker_modules=34,max_lean_seconds=max(v['seconds'] for v in lean.values()),max_group_rss_kib=max(v['peak_group_rss_kib'] for v in lean.values()),sum_process_wall_seconds=sum(v['seconds'] for v in lean.values()))
(L/'replay-summary.json').write_text(json.dumps(summary,indent=2));print(summary)
net={str(p.relative_to(L)):sha(p) for p in (L/'downloads').rglob('*') if p.is_file()};(L/'network-sha256.json').write_text(json.dumps(net,indent=2))
# Final manifest excludes itself and transient build products.
manifest={str(p.relative_to(L)):sha(p) for p in L.rglob('*') if p.is_file() and p.name!='artifacts-sha256.json' and not (p.parent.name=='logs' and p.name.startswith('finalize.')) and not any(s in p.parts for s in ['build','first-build'])}
(L/'artifacts-sha256.json').write_text(json.dumps(manifest,indent=2))
