from work import *
m=json.loads((L/'final-manifest.json').read_text());fail=[]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json'] and '__pycache__' not in p.parts}
if actual!=set(m):fail.append('manifest membership: extra=%s missing=%s'%(sorted(actual-set(m)),sorted(set(m)-actual)))
for k,h in m.items():
    if (L/k).exists() and sha(L/k)!=h:fail.append('changed '+k)
for line in (L/'bindings.jsonl').read_text().splitlines():
    r=json.loads(line)
    if sha(r['copy'])!=r['sha256']:fail.append('copy '+r['copy'])
    if not r['administrative'] and sha(r['original'])!=r['sha256']:fail.append('original '+r['original'])
for r in json.loads((L/'derived-text-bindings.json').read_text()):
    for k in ['pdf','text']:
        if sha(L/r[k])!=r[k+'_sha256']:fail.append('derived '+r[k])
hc=json.loads((L/'history-coverage.json').read_text())
idx=json.loads(open(hc['index']).read())
if sha(hc['index'])!=hc['index_sha256']:fail.append('history index')
hf=sum(1 for r in idx['verified_references'] if not pathlib.Path(r['path']).exists() or sha(r['path'])!=r['sha256'])
if hf:fail.append('history refs %d'%hf)
if (L/'PROOF.md').exists():fail.append('unexpected PROOF.md')
rec=dict(status='PASS' if not fail else 'FAIL',failures=fail,manifest_files=len(m),manifest_sha256=sha(L/'final-manifest.json'),history_verified=len(idx['verified_references'])-hf,administrative_originals='snapshots only; not compared',utc=now())
save(L/'verification-receipt.json',rec);print(json.dumps(rec,indent=1))
