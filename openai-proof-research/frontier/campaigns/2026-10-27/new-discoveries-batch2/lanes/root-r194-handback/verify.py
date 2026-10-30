from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r194'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
if isinstance(m['files'],dict):
 for n,h in m['files'].items():assert sha(S/n)==h,n
 names=set(m['files']);excluded=m['excluded']
else:
 for n,h,z in m['files']:assert sha(S/n)==h and (S/n).stat().st_size==z,n
 names={n for n,h,z in m['files']};excluded=m['explicit_exclusions']
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(excluded)==names
science=json.loads((S/'scientific-freeze.json').read_text())
if isinstance(science,list):
 bindings=[(r['original'],r['copy'],r['sha256'],None) for r in science]
else:
 for n,h,z in science['files']:assert sha(S/n)==h and (S/n).stat().st_size==z
 bindings=json.loads((S/'scientific-input-freeze.json').read_text())['bindings']
def originals():
 for n,c,h,z in bindings:
  for p in [Path(n),S/c]:assert sha(p)==h and (z is None or p.stat().st_size==z),str(p)
originals()
g=S/'guard-binding.json'
if g.exists():
 j=json.loads(g.read_text());assert sha(Path(j['path']))==j['sha256']
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(names),scientific_original_copy_pairs=len(bindings),frozen_files=len(freeze),private_replay='byte-identical',qualification='Exact method controls only; no universal proof or source counterexample.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
