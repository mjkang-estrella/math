from pathlib import Path
import json,hashlib,subprocess,sys,datetime
D=Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
entries=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in excluded:
  b=p.read_bytes();entries.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':entries},indent=2)+'\n')
results=[]
for mode in ['hash','size','extra']:
 r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--negative',mode],capture_output=True,text=True)
 assert r.returncode!=0
 results.append({'mode':mode,'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,(r.stdout,r.stderr)
result=json.loads(r.stdout)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'positive':result,'negative_tests':results,'guard':'caller uses original fixed helper_guard.py; 512MiB AS/group RSS, CPU210s, wall230s unchanged','math_pass':False,'novelty_pass':False}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
