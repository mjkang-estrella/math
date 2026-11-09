import json,pathlib,hashlib,subprocess,datetime,sys
L=pathlib.Path(__file__).resolve().parent
assert not (L/'final-receipt.json').exists(),'refuse to alter receipt'
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name!='manifest.json':files.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'schema':1,'files':files,'excluded':['manifest.json (self)','final-receipt.json (separate receipt)']},indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(L/'verify.py')],capture_output=True,text=True)
if p.returncode:print(p.stdout,p.stderr);sys.exit(p.returncode)
r=json.loads(p.stdout);r.update(manifest_sha256=hashlib.sha256((L/'manifest.json').read_bytes()).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verification='independent lane verifier; all original flat refs and exact payload',resource_policy='helper_guard.py; 512MiB/CPU210s/wall230s; no limit changes')
(L/'final-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
