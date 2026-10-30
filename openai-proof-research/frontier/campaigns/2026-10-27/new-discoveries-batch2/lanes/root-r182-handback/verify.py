from pathlib import Path
import hashlib,json,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r182'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(p,r):assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((S/name).read_text());names=[]
 for r in j['records']:check(S/r['path'],r);names.append(r['path'])
 assert len(names)==len(set(names));counts[name]=len(names)
 if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['exclusions'])==set(names)
for r in json.loads((S/'original-copy-provenance.json').read_text()):
 a=S.parents[5]/r['original'];b=S/r['copy'];assert a.read_bytes()==b.read_bytes() and sha(b)==r['sha256']
g=json.loads((S/'guard-binding.json').read_text());assert sha(Path(g['path']))==g['sha256']
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.log').open('w') as log:subprocess.run([sys.executable,str(P/'checks.py')],stdout=log,stderr=subprocess.STDOUT,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:check(Path(r['path']),r)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',verified=counts,frozen_files=len(freeze),private_exact_replay='byte-identical',qualification='Exact finite-field identities and collisions for e=3..7 only; universal odd-degree collision theorem and effective curve bounds remain missing.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
