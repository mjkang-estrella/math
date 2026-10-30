from pathlib import Path
import hashlib,json,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-dsbs-negative-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text());listed={r['path'] for r in m['files']}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-{'finalmanifest.json','finalmanifest-verification.json'}==listed
for r in m['files']:check(S/r['path'],r)
before=json.loads((S/'before-hashes.json').read_text())['files']
for r in before:check(Path(r['path']),r)
shutil.copyfile(S/'independent_checks.py',P/'independent_checks.py')
with (P/'checks.log').open('w') as log:subprocess.run([sys.executable,str(P/'independent_checks.py')],stdout=log,stderr=subprocess.STDOUT,check=True)
assert (P/'independent-checks.json').read_bytes()==(S/'independent-checks.json').read_bytes()
for r in freeze:check(Path(r['path']),r)
for r in before:check(Path(r['path']),r)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',review_manifest_entries=len(listed),frozen_review_files=len(freeze),originals_reverified=len(before),independent_diagnostics='byte-identical private replay',qualification='Exact rational probability identities plus high-precision entropy diagnostics; no formal or novelty clearance')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
