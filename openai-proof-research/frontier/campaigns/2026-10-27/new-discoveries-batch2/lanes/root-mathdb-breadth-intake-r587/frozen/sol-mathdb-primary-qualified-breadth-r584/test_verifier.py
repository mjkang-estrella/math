from pathlib import Path
import tempfile,hashlib,json,subprocess,sys
D=Path(__file__).parent;out=[]
for kind in ['valid','hash','size','extra']:
 with tempfile.TemporaryDirectory(dir=D,prefix='negative-fixture-') as t:
  p=Path(t);b=b'tiny immutable fixture\n';(p/'item').write_bytes(b);e={'path':'item','size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
  if kind=='hash':e['sha256']='0'*64
  if kind=='size':e['size']+=1
  m={'files':[e],'excluded_exact_paths':['manifest.json','final-verification-receipt.json']};(p/'manifest.json').write_text(json.dumps(m))
  if kind=='extra':(p/'extra').write_text('reject')
  r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--payload-only',str(p)],capture_output=True,text=True);assert (r.returncode==0)==(kind=='valid')
  out.append({'case':kind,'exit':r.returncode,'stderr':r.stderr.strip(),'expected_result_observed':True})
(D/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
