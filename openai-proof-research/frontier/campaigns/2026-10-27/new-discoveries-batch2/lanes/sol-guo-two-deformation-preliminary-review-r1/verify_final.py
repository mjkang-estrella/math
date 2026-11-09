from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(m)
for name,digest in m.items():assert h(L/name)==digest,name
p=json.loads((L/'provenance.json').read_text())
for row in p['scientific_before_after']:
 assert h(Path(row['original']))==h(L/row['copy'])==row['sha256'],row['copy']
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_sha256=h(L/'manifest.json'),files=len(m),scientific_original_copy_rechecks=len(p['scientific_before_after']),administrative='snapshot only',manifest_excludes=['manifest.json','verification-receipt.json'])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
