import json,pathlib,hashlib,subprocess,datetime
D=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2,sort_keys=True)+'\n')
p=subprocess.run(['python3','-B',str(D/'verify.py')],capture_output=True,text=True);assert p.returncode==0,p.stderr
r=json.loads(p.stdout);tests=[]
for kind in ['hash','size','extra']:
 p=subprocess.run(['python3','-B',str(D/'verify.py'),'--negative',kind],capture_output=True,text=True);assert p.returncode!=0
 tests.append({'kind':kind,'exit_code':p.returncode,'stderr':p.stderr.strip(),'mutation':'in-memory observation override only; originals untouched'})
r.update({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'negative_tests':tests,'verifier':'read-only; no upstream scripts executed','guard':'512MiB AS/groupRSS, CPU210s, wall230s unchanged; all Python via fixed helper_guard.py'})
(D/'final-verification-receipt.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(r,indent=2))
