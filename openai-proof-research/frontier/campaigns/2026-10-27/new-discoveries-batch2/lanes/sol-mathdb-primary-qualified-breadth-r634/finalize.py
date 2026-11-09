from pathlib import Path
import json,hashlib,subprocess,sys,datetime
O=Path(__file__).resolve().parent

def w(n,v):(O/n).write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def manifest():
 files=[]
 for p in sorted(O.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 w('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
w('negative-tests.json',{'pending':True});w('final-verification-receipt.json',{'pending':True});manifest()
results=[]
for mode in ['hash','size','extra']:
 p=subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--negative',mode],capture_output=True,text=True,timeout=40)
 assert p.returncode!=0,(mode,p.stdout,p.stderr)
 results.append({'mode':mode,'exit_code':p.returncode,'stderr':p.stderr.strip(),'in_memory_only':True})
w('negative-tests.json',results);manifest()
p=subprocess.run([sys.executable,'-B',str(O/'verify.py')],capture_output=True,text=True,timeout=70)
assert p.returncode==0,p.stderr
result=json.loads(p.stdout);b=(O/'manifest.json').read_bytes();result.update({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'payload_files':len(json.loads(b)['files']),'negative_tests':results,'guard':'fixed helper_guard.py; entire finalizer and verifier children under same capped process group'})
w('final-verification-receipt.json',result);print(json.dumps(result,sort_keys=True))
