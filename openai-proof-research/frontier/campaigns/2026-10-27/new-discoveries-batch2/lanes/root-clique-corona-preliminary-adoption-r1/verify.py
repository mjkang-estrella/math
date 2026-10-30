from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-clique-corona-preliminary-review-r1'
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(r,p):assert Path(p).stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
m=json.loads((S/'final-manifest.json').read_text())
for r in m['files']:check(r,S/r['path'])
assert {r['path'] for r in m['files']}=={str(p.relative_to(S)) for p in S.rglob('*') if p.is_file() and str(p.relative_to(S)) not in m['exclusions']}
rows=json.loads((S/'before-freeze.json').read_text())['files']
for r in rows:
 check(r,r['path']);check(r,r['copy'])
assert len(rows)==71 and len(m['files'])==108
D=P/'own-check';D.mkdir(exist_ok=True);shutil.copyfile(S/'check.py',D/'check.py')
with (P/'checker.log').open('w') as f:subprocess.run([sys.executable,str(D/'check.py')],check=True,stdout=f,stderr=subprocess.STDOUT)
assert (D/'own-checks.json').read_bytes()==(S/'own-checks.json').read_bytes()
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','originals':71,'manifest':108,'review_files':len(files),'own_checker_byte_identical':True,'credit':0}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
