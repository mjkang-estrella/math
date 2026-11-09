import pathlib,json,hashlib,subprocess,sys,datetime
D=pathlib.Path(__file__).resolve().parent
ex=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in ex:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':ex,'files':files},indent=2)+'\n')
# Every checker subprocess stays under the outer fixed process-group guard.
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
negative=[]
for kind in ['hash','size','extra']:
 p=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--negative',kind],capture_output=True,text=True)
 assert p.returncode!=0
 negative.append({'mutation':kind,'exit':p.returncode,'stderr':p.stderr.strip(),'originals_mutated':False,'mechanism':'in-memory manifest or discovered-file-set perturbation; same payload checker'})
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verification':json.loads(r.stdout),'negative_tests':negative,'limits':'fixed helper_guard.py unchanged; 512MiB AS/groupRSS, CPU210s wall230s','mathematical_acceptance':False}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
