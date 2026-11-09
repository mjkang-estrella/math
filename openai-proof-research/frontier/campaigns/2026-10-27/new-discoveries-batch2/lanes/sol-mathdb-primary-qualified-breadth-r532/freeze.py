from pathlib import Path
import json,hashlib,subprocess,sys,datetime
D=Path(__file__).resolve().parent
def save(n,x):(D/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
save('manifest.json',{'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files})
b=(D/'manifest.json').read_bytes();r={'manifest':{'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'state':'PENDING'};save('verification-receipt.json',r)
x=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True);r.update(state='PASS' if x.returncode==0 else 'FAIL',exit_code=x.returncode,verifier_stdout=x.stdout,verifier_stderr=x.stderr,payload_files=len(files),scientific_acceptance=False);save('verification-receipt.json',r);print(json.dumps(r));sys.exit(x.returncode)
