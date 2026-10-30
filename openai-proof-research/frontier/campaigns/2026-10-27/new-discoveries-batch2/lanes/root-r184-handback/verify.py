from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r184'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n');counts={}
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((S/name).read_text())
 for n,h in j['records'].items():assert sha(S/n)==h,n
 assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(j['exclusions'])==set(j['records'])
 counts[name]=len(j['records'])
j=json.loads((S/'external-scientific-freeze.json').read_text())
for n,h in j['records'].items():assert sha(Path(n) if n.startswith('/') else S.parents[5]/n)==h,n
counts['external']=len(j['records']);shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.log').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,stderr=subprocess.STDOUT,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
for r in freeze:
 p=Path(r['path']);assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
out=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=counts,frozen_files=len(freeze),private_exact_replay='byte-identical',qualification='Symbolic Liouville/Sonin identities and hypothetical-envelope obstruction only; neither source conjecture resolved.')
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
