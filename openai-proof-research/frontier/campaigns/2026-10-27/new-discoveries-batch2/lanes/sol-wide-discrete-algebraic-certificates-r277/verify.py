from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text());errors=[]
for n,h in m.items():
 if not (L/n).is_file() or sha(L/n)!=h:errors.append(n)
files={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
assert files==set(m),(files-set(m),set(m)-files)
rows=json.loads((L/'bindings.json').read_text())
for row in rows:
 if sha(Path(row['original']))!=row['sha256']:errors.append(row['original'])
 if 'copy' in row and sha(L/row['copy'])!=row['sha256']:errors.append(row['copy'])
for row in json.loads((L/'source-access-bindings.json').read_text())['primary']:
 assert sha(L/'sources'/(row['id']+'.pdf'))==row['pdf_sha256']
 assert sha(L/'sources'/(row['id']+'.txt'))==row['text_sha256']
assert not (L/'PROOF.md').exists()
c=json.loads((L/'exact-checks.json').read_text());assert c['lift_search']['tested']==240 and c['lift_search']['consistent']==0
r=dict(status='PASS' if not errors else 'FAIL',errors=errors,files=len(m),original_bindings=len(rows),manifest_sha256=sha(L/'MANIFEST.json'),at=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='separate guarded after-write verification; hashes/source copies/originals/artifact coverage; not independent mathematical review')
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r));assert not errors
