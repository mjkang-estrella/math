from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r181'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
j=json.loads((S/'scientific-freeze.json').read_text())
for key,base in [('local',S),('originals',Path('/'))]:
 for n,h,z in j[key]:assert sha(base/n)==h and (base/n).stat().st_size==z,n
 counts[key]=len(j[key])
j=json.loads((S/'finalmanifest.json').read_text())
for n,h,z in j['records']:assert sha(S/n)==h and (S/n).stat().st_size==z,n
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['exclusions'])=={r[0] for r in j['records']}
counts['manifest']=len(j['records']);shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.log').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,stderr=subprocess.STDOUT,check=True)
a=json.loads((P/'checks.json').read_text());b=json.loads((S/'checks.json').read_text());a.pop('utc');b.pop('utc');assert a==b
for r in freeze:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,frozen_files=len(freeze),private_exact_replay='All mathematical output fields identical; UTC excluded',qualification='Exact positive-test diagnostic of prior public refutation only; no new result or current-registry clearance.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
