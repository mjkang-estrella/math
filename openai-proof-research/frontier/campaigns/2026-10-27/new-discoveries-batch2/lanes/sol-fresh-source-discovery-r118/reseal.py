"""Preserve stale delivery-manifest failure; never alter source-lock baseline."""
from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(131072),b''):h.update(b)
 return h.hexdigest()
p=L/'finalmanifest.json';q=L/'initial-manifest-stale.json'
if not q.exists():q.write_bytes(p.read_bytes())
old=json.loads(q.read_text())
diff=[r['path'] for r in old if sha(L/r['path'])!=r['sha256']]
(L/'manifest-failure.json').write_text(json.dumps({'failed_check':'verify_manifest.py AssertionError: SUMMARY.md','guard_exit':1,'peakRSS':28733440,'wall':0.080267644,'cause':'seal.py entire body was initialization-only; rerun did not update delivery manifest after summary/progress/check-result edits','old_manifest':'initial-manifest-stale.json','old_sha256':sha(q),'old_binding_differences':diff,'source_lock_unchanged':not any(x.startswith('sources/') or x=='source-lock.json' for x in diff)},indent=2))
for r in json.loads((L/'source-lock.json').read_text()):assert sha(L/r['copy'])==r['sha256'],r['copy']
rows=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(L.rglob('*')) if p.is_file() and p.name!='finalmanifest.json']
(L/'finalmanifest.json').write_text(json.dumps(rows,indent=2));print('new delivery manifest',len(rows),'source lock unchanged')
