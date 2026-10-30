from pathlib import Path
import hashlib,json,shutil,subprocess,sys,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r177'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
for name in ['scientific-freeze.json','finalmanifest.json','primary-hashes.json']:
 j=json.loads((S/name).read_text());names=[]
 for r in j['records']:
  p=S/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'];names.append(r['path'])
 assert len(names)==len(set(names));counts[name]=len(names)
 if name=='finalmanifest.json':assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['exclusions'])==set(names)
for script,output in [('checks.py','checks.json'),('tree_route.py','tree-route.json')]:
 shutil.copyfile(S/script,P/script)
 with (P/(script+'.log')).open('w') as log:subprocess.run([sys.executable,str(P/script)],stdout=log,stderr=subprocess.STDOUT,check=True)
 assert (P/output).read_bytes()==(S/output).read_bytes()
for r in freeze:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,frozen_files=len(freeze),private_exact_replay='Both outputs byte-identical',qualification='770 bounded graph minima and 18247 restricted tree constructions; no universal walk theorem or novelty clearance.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
