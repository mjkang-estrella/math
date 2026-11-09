import pathlib,json,hashlib,subprocess,datetime
D=pathlib.Path(__file__).resolve().parent
ex=['manifest.json','final-verification-receipt.json']
def put(n,x):(D/n).write_text(json.dumps(x,indent=2)+'\n')
def manifest():
 rows=[]
 for p in sorted(D.rglob('*')):
  if p.is_file() and str(p.relative_to(D)) not in ex:
   b=p.read_bytes();rows.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 put('manifest.json',{'excluded_exact_paths':ex,'files':rows})
manifest();tests=[]
for mode in ['--negative-hash','--negative-size','--negative-extra']:
 r=subprocess.run(['python3','-B',str(D/'verify.py'),mode],capture_output=True,text=True);assert r.returncode!=0;tests.append({'mode':mode,'exit':r.returncode,'stderr':r.stderr.strip(),'method':'in-memory overlay only; originals unmodified'})
put('negative-tests.json',tests);manifest()
r=subprocess.run(['python3','-B',str(D/'verify.py')],capture_output=True,text=True)
print(r.stdout,r.stderr);assert r.returncode==0
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'result':json.loads(r.stdout),'negative_tests':tests,'guard':'helper_guard.py fixed512MiB CPU210 wall230; all child helpers inherit resource limits'}
put('final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2))
