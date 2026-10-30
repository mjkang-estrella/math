"""Separate post-write verifier. Invoke under the assigned helper guard."""
from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
assert set(m['exclusions'])=={'manifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['exclusions'])
assert actual==set(m['files']),('inventory mismatch',actual^set(m['files']))
for n,h in m['files'].items():assert sha(L/n)==h,n
b=json.loads((L/'scientific-bindings.json').read_text())
for r in b['primary']:
 assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256']
g=b['guard'];assert sha(Path(g['original']))==sha(L/g['copy'])==g['sha256']
h=json.loads((L/'historical-after.json').read_text())
for r in h['records']:
 p=Path(r['snapshot']);p=p if p.is_absolute() else L/p
 assert sha(p)==r['expected']==r['snapshot_sha256']
aliases=json.loads((L/'alias-screen.json').read_text())
for r in aliases['records']:
 if not r.get('missing'):assert sha(Path(r['snapshot']))==r['sha256']
assigned=json.loads((L/'assigned-bindings.json').read_text())
for r in assigned:assert sha(L/r['copy'])==r['sha256']
c=json.loads((L/'checks.json').read_text());assert c['status']=='PASS'
edges=0
for g in c['graphs']:
 ds=g.get('witness',[]);n=g['n']
 if ds:
  assert len(set(map(tuple,ds)))==len(ds)
  assert all(len(d)==n and min(d)>=1 and max(d)<=n for d in ds)
  assert all(sum(x>y for x in ds[i] for y in ds[(i+1)%len(ds)])==n*n//2+1 for i in range(len(ds)))
  edges+=len(ds)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(L/'manifest.json'),'files':len(m['files']),'scientific_pairs':len(b['primary']),'history_snapshots':len(h['records']),'aliases':len(aliases['records']),'witness_edges_rechecked':edges,'limits':'Integrity and finite arithmetic only, not a proof or novelty certificate. Missing separate pre-read scientific disk check remains documented. Historical live drift is reported, not bound as immutable science.'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
