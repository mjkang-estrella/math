"""Separate final manifest and source verification. Does not modify bound files."""
from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());files=m['files']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excluded']}
assert actual==set(files)
for name,h in files.items():assert sha(L/name)==h,name
rows=json.loads((L/'scientific-hashes.json').read_text())['scientific_files']
for r in rows:
 assert r['sha256_before']==r['sha256_original_after']==r['sha256_copy_after']==sha(Path(r['original']))==sha(L/r['copy'])
assert json.loads((L/'exact-check.json').read_text())['status']=='PASS'
out={'status':'PASS','verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'manifest_sha256':sha(L/'manifest.json'),'manifest_bound_files':len(files),
 'scientific_original_copy_pairs':len(rows),'source_before_after_equal':True,
 'scope':'integrity verification, not novelty clearance or campaign acceptance',
 'counts':{'additional':9,'total':39,'next':40}}
(L/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
