from pathlib import Path
import hashlib,json,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r171'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):
 assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
a=json.loads((S/'scientific-freeze.json').read_text());m=json.loads((S/'finalmanifest.json').read_text())
for r in a['files']:check(S/r['path'],r)
for r in a['external_fixed_inputs']:check(Path(r['path']),r)
for r in m['files']:check(S/r['path'],r)
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.log').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,stderr=subprocess.STDOUT,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:check(Path(r['path']),r)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',scientific_files=len(a['files']),manifest_files=len(m['files']),frozen_files=len(freeze),external_inputs=len(a['external_fixed_inputs']),bounded_replay='byte-identical private copy',scope='Integrity and finite diagnostics only; no characteristic-zero universal rank proof or novelty clearance')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
