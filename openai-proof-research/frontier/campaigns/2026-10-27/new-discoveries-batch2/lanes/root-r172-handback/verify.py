from pathlib import Path
import hashlib,json,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r172'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
counts={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((S/name).read_text());names=[]
 for r in j['records']:check(S/r['path'],r);names.append(r['path'])
 assert len(names)==len(set(names));counts[name]=len(names)
 if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file() and p.name not in j['exclude']}==set(names)
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.log').open('w') as log:subprocess.run([sys.executable,str(P/'checks.py')],stdout=log,stderr=subprocess.STDOUT,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:check(Path(r['path']),r)
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',verified=counts,frozen_files=len(freeze),private_replay='byte-identical',scope='Exact finite method obstruction and known published example; no universal source resolution')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
