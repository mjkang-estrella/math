import pathlib,hashlib,json,subprocess,datetime,sys
O=pathlib.Path(__file__).resolve().parent
# File writes stay exclusively in this lane. No upstream verifier is executed.
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def freeze():
 files=[]
 for p in sorted(O.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 dump(O/'manifest.json',{'files':files,'excluded_exact_paths':['manifest.json','final-verification-receipt.json']})
 b=(O/'manifest.json').read_bytes();dump(O/'final-verification-receipt.json',{'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'stage':'pre-final verification binding'})
dump(O/'negative-tests.json',{'pending':True});dump(O/'final-verification-receipt.json',{'pending':True});freeze()
initial=subprocess.run([str(O/'verify.sh')],capture_output=True,text=True);assert initial.returncode==0,initial.stderr
negative=[]
for kind in ['hash','size','extra']:
 r=subprocess.run([str(O/'verify.sh'),'--negative-test',kind],capture_output=True,text=True)
 assert r.returncode!=0 and 'mismatch' in r.stderr,(kind,r.stdout,r.stderr)
 negative.append({'test':kind,'mode':'in-memory mutation of verifier-observed digest/size/path set; no file mutation','exit_code':r.returncode,'stderr':r.stderr.strip(),'rejected':True})
dump(O/'negative-tests.json',negative);freeze()
r=subprocess.run([str(O/'verify.sh')],capture_output=True,text=True);assert r.returncode==0,r.stderr
result=json.loads(r.stdout.strip());dump(O/'final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verifier_exit':r.returncode,'manifest_sha256':result['manifest_sha256'],'manifest_size':result['manifest_size'],'result':result,'negative_tests':'hash/size/extra all rejected nonzero; virtual mutations, originals unchanged','guard_stderr':r.stderr.strip(),'scientific_acceptance':'HOLD; integrity only'})
r2=subprocess.run([str(O/'verify.sh')],capture_output=True,text=True);assert r2.returncode==0,r2.stderr
print(r2.stdout.strip());print('FINAL receipt written; all negatives rejected')
