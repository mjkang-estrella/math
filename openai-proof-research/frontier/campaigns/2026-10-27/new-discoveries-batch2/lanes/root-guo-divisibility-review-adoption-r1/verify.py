from pathlib import Path
import json,hashlib,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-guo-divisibility-preliminary-review-r1'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'final-manifest.json').read_text())
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['explicit_exclusions'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
inputs=json.loads((S/'freeze-before.json').read_text())['scientific_pairs']
for r in inputs:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
shutil.copyfile(S/'checker.py',P/'checker.py')
with (P/'checker.log').open('w') as f:subprocess.run([sys.executable,str(P/'checker.py')],stdout=f,stderr=subprocess.STDOUT,check=True)
a=json.loads((P/'checker-evidence.json').read_text());b=json.loads((S/'checker-evidence.json').read_text());a.pop('utc');b.pop('utc');assert a==b
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
for r in inputs:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256']
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_files=len(m['files']),frozen_review_files=len(freeze),input_original_copy_pairs=len(inputs),private_replay='identical except UTC',qualification='Finite arithmetic and integrity; ordinary proof and substantive judgment separate from novelty/formal acceptance.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
