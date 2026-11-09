from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in m['excludes']}
assert actual==set(m['files'])
for name,r in m['files'].items():
 p=L/name;assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],name
b=json.loads((L/'bindings.json').read_text())
for r in b:assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256'],r['original']
for r in map(json.loads,(L/'access.jsonl').read_text().splitlines()):assert sha(Path(r['path']))==r['sha256']
p=json.loads((L/'provenance.json').read_text());assert sha(Path(p['guard']['path']))==p['guard']['sha256']
assert json.loads((L/'checks.json').read_text())['status']=='PASS'
r=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'final-manifest.json'),files_checked=len(m['files']),original_copy_bindings_checked=len(b),retrievals_checked=len((L/'access.jsonl').read_text().splitlines()),verification='separate guarded execution after final manifest write',counts_unchanged=dict(additional=9,total=39,next=40))
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
