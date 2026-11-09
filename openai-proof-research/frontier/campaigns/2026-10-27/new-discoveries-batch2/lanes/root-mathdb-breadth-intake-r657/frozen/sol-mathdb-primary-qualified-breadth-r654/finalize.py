from pathlib import Path
import hashlib,json,subprocess,datetime
O=Path(__file__).resolve().parent
ex=['manifest.json','final-verification-receipt.json']
def bind(p):return {'path':str(p.relative_to(O)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
def freeze():
 files=[bind(p) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in ex]
 (O/'manifest.json').write_text(json.dumps({'excluded_exact_paths':ex,'files':files},indent=2)+'\n')
# First freeze needed so negative tests exercise the actual manifest validator.
freeze();neg=[]
for mode in ['hash','size','extra']:
 r=subprocess.run(['python3','-B',str(O/'verify.py'),mode],capture_output=True,text=True)
 assert r.returncode!=0 and 'mismatch' in r.stderr,(mode,r.stdout,r.stderr)
 neg.append({'mutation':mode,'exit':r.returncode,'stderr':r.stderr.strip(),'originals_mutated':False,'method':'virtual override inside exact payload validator'})
(O/'negative-tests.json').write_text(json.dumps(neg,indent=2)+'\n');freeze()
r=subprocess.run(['python3','-B',str(O/'verify.py')],capture_output=True,text=True)
print(r.stdout,r.stderr);assert r.returncode==0
m=bind(O/'manifest.json');receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':m,'verification':json.loads(r.stdout),'negative_tests':neg,'guard':'Fixed helper_guard.py enclosing this script and its subprocesses; 512MiB AS/groupRSS CPU210s wall230s unchanged.'}
(O/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(m))
