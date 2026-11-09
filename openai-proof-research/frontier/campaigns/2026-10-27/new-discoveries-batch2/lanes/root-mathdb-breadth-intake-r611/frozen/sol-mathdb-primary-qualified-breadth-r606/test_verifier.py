from pathlib import Path
import tempfile,json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent;out=[]
for case in ['valid','hash','size','extra']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=D) as t:
  p=Path(t);b=b'fixture';(p/'x').write_bytes(b)
  x={'path':'x','sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
  if case=='hash':x['sha256']='0'*64
  if case=='size':x['size']+=1
  if case=='extra':(p/'unexpected').write_text('extra')
  (p/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[x]}))
  r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--payload-only',str(p)],capture_output=True,text=True)
  assert (r.returncode==0)==(case=='valid'),(case,r.stdout,r.stderr)
  out.append({'case':case,'exit':r.returncode,'expected_rejection':case!='valid','stderr':r.stderr.strip().replace(str(p),'<lane-local-fixture>')})
(D/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
