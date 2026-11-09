from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert actual==set(m['sha256'])
for name,h in m['sha256'].items():assert sha(L/name)==h,name
b=json.loads((L/'binding-before.json').read_text())
for r in b['files']:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
p=json.loads((L/'provenance.json').read_text());assert sha(Path(p['guard']))==p['guard_sha256']
for r in p['retrievals']:
 if 'sha256' in r:
  q=L/r['derived'] if 'derived' in r else L/'sources'/r['name']
  assert sha(q)==r['sha256']
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_sha256=sha(L/'manifest.json'),manifest_entries=len(actual),original_copy_bindings=len(b['files']),download_and_extraction_bindings='PASS',guard_binding='PASS',manifest_exclusions=m['excludes'],expensive_coefficient_replay=False,count_credit=0)
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt))
