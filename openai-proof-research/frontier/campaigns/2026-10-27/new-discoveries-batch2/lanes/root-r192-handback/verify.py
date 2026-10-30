from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r192'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
rows=json.loads((S/'scientific-freeze.json').read_text())
for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
m=json.loads((S/'finalmanifest.json').read_text())
for n,h in m['files'].items():assert sha(S/n)==h
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['exclusions'])==set(m['files'])
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_pairs=len(rows),manifest_entries=len(m['files']),frozen_files=len(freeze),private_replay='byte-identical',qualification='Exact finite controls and method obstructions only; no all-space linear retraction theorem.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
