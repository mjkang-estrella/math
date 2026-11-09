import pathlib,hashlib,json,subprocess,datetime
O=pathlib.Path(__file__).resolve().parent

def manifest():
 files=[]
 for p in sorted(O.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 (O/'manifest.json').write_text(json.dumps({'files':files,'excluded_exact_paths':['manifest.json','final-verification-receipt.json']},indent=2)+'\n')
manifest()
neg=[]
for mode in ['hash','size','extra']:
 r=subprocess.run(['python3','-B',str(O/'verify.py'),'--negative',mode],capture_output=True,text=True);assert r.returncode!=0
 neg.append({'injection':mode,'exit_code':r.returncode,'stderr':r.stderr.strip(),'originals_mutated':False,'method':'in-memory manifest expectation or file-set injection; same verifier checks'})
(O/'negative-tests.json').write_text(json.dumps(neg,indent=2)+'\n');manifest()
r=subprocess.run(['python3','-B',str(O/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
b=(O/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verification':json.loads(r.stdout),'negative_tests':neg,'guard':'fixed helper_guard.py enclosing this process and all subprocesses; 512MiB AS/groupRSS CPU210 wall230','excluded_receipt':'final-verification-receipt.json'}
(O/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
