from pathlib import Path
import json,subprocess,sys,hashlib,shutil
D=Path(__file__).resolve().parent;T=D/'negative-fixture';T.mkdir(exist_ok=False)
try:
 p=T/'payload';p.write_bytes(b'original')
 m={'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':[{'path':'payload','size':8,'sha256':hashlib.sha256(b'original').hexdigest()}]};(T/'manifest.json').write_text(json.dumps(m));out=[]
 for mode in ['valid','hash','size','extra']:
  p.write_bytes(b'changed!' if mode=='hash' else b'original!extra' if mode=='size' else b'original')
  if mode=='extra':(T/'unexpected').write_text('extra')
  r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--payload-only','--root',str(T)],capture_output=True,text=True)
  out.append({'mode':mode,'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr});assert (r.returncode==0)==(mode=='valid'),out
 (D/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
finally:shutil.rmtree(T)
