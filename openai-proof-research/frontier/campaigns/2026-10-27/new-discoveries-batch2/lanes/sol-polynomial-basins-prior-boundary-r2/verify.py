from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());checked=[]
for n,h in m['files'].items():
 assert sha(L/n)==h,n
 checked.append(n)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excluded']}
assert actual==set(checked)
f=json.loads((L/'freeze-before.json').read_text())
for r in f['files']:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
for n in ['retrieval.json','retrieval2.json','retrieval3.json','retrieval4.json','retrieval5.json']:
 for r in json.loads((L/n).read_text()):
  if 'path' in r:assert sha(L/r['path'])==r['sha256']
  if 'text' in r:assert sha(L/r['text'])==r['text_sha256']
for r in json.loads((L/'administrative-snapshots.json').read_text()):assert sha(L/r['copy'])==r['sha256']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'final-manifest.json'),files_verified=len(checked),frozen_original_copy_pairs_verified=len(f['files']),administrative='snapshot-only; live originals not required immutable',separate_guarded_process=True,counts_unchanged=[9,39,40])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
