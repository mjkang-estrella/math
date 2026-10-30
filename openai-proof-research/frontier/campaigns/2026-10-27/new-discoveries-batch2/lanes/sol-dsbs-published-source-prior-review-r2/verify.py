"""Offline verifier. Run only through the unchanged campaign helper_guard.py."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,datetime,sys
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((L/'before-hashes.json').read_text())
after=[]
for r in rows:
 a=h(Path(r['original']));b=h(L/r['copy'])
 assert a==b==r['sha256']==r['copy_sha256'],r
 after.append(dict(original=r['original'],copy=r['copy'],original_sha256=a,copy_sha256=b))
# Exact non-memoryless processors, with zeros in components, positive mixture.
A=[[F(2,5),F(1,5),F(1,5),F(1,5)],[F(0),F(1,3),F(1,3),F(1,3)]]
B=[[F(1,4)]*4,[F(1,2),F(0),F(0),F(1,2)]]
assert A[0][0]*A[0][3]!=A[0][1]*A[0][2]
assert B[1][0]*B[1][3]!=B[1][1]*B[1][2]
Q=[F(3,10),F(1,5),F(1,5),F(3,10)]
P={(x,y):sum(A[m][x]*B[m][y]/2 for m in range(2)) for x in range(4) for y in range(4)}
hat={}
for x in range(4):
 for y in range(4):
  u0=2*(x//2)+y//2;u1=2*(x%2)+y%2
  q=Q[u0]*Q[u1]
  for m in range(2):hat[m,x,y]=q*A[m][x]*B[m][y]/(2*P[x,y])
  assert sum(hat[m,x,y] for m in range(2))==q
assert sum(hat.values())==1
for receipt in sorted((L/'retrieved').glob('*.receipt.json')):
 r=json.loads(receipt.read_text());p=L/'retrieved'/r['name']
 assert h(p)==r['sha256'] and p.stat().st_size==r['bytes']
v=json.loads((L/'primarybody-versions.json').read_text())
for r in v:
 if r.get('body'):assert h(L/r['body'])==r['sha256']
if (L/'finalmanifest.json').exists():
 manifest=json.loads((L/'finalmanifest.json').read_text())
 for r in manifest:assert h(L/r['path'])==r['sha256'],r['path']
 # Detect added or removed payload, not only changed recorded files.
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','final-verification.json']}
 assert actual=={r['path'] for r in manifest}
else:manifest=[]
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',originals_and_copies=len(rows),manifest_entries=len(manifest),exact_correlated_block_posterior_controls=16,live_NEXT_invariant=False,qualification='Exact probability identities and byte integrity only; no numerical or formal proof of novelty.')
if '--check-only' not in sys.argv:
 (L/'after-hashes.json').write_text(json.dumps(after,indent=2)+'\n')
 (L/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
else:(L/'final-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
