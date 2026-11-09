from work import *
manifest=json.loads((L/'final-manifest.json').read_text());fail=[]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
if actual!=set(manifest):fail.append('manifest membership')
for name,h in manifest.items():
 if sha(L/name)!=h:fail.append(name)
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line)
 if sha(pathlib.Path(r['copy']))!=r['sha256']:fail.append('copy '+r['copy'])
 if not r['administrative'] and sha(pathlib.Path(r['original']))!=r['sha256']:fail.append('original '+r['original'])
for r in json.loads((L/'derived-text-bindings.json').read_text()):
 for k in ['pdf','text']:
  if sha(L/r[k])!=r[k+'_sha256']:fail.append('derived '+r[k])
history=json.loads((L/'history-verification.json').read_text())
for r in history:
 if sha(pathlib.Path(r['path']))!=r['expected']:fail.append('history '+r['path'])
assert not (L/'PROOF.md').exists()
receipt=dict(status='PASS' if not fail else 'FAIL',failures=fail,files=len(manifest),manifest_sha256=sha(L/'final-manifest.json'),history_verified=len(history),administrative_originals='not compared: snapshots only',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
save(L/'verification-receipt.json',receipt);print(json.dumps(receipt,indent=2));assert not fail
