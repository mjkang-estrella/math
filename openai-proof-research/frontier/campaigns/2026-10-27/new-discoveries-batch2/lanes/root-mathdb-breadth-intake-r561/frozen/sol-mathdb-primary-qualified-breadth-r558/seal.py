from pathlib import Path
import json,hashlib,tempfile,subprocess,datetime,os
D=Path(__file__).resolve().parent
EX=['manifest.json','final-verification-receipt.json']
def rec(p):
 b=p.read_bytes();return {'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
# Additional flat bindings are established before re-reading their contents.
f= D/'flat-bindings.json';refs=json.loads(f.read_text())
for p in [D.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',D.parent/'pi-mathdb-full-corpus-inventory-r301/manifest.json']:
 b=p.read_bytes();refs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
save(f,list({r['path']:r for r in refs}.values()))
results=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=D) as t:
 T=Path(t);a=T/'a.txt';a.write_bytes(b'abc')
 base={'excluded_exact_paths':EX,'files':[{'path':'a.txt','size':3,'sha256':hashlib.sha256(b'abc').hexdigest()}]}
 for kind in ['positive','hash','size','extra']:
  m=json.loads(json.dumps(base))
  if kind=='hash':m['files'][0]['sha256']='0'*64
  if kind=='size':m['files'][0]['size']=4
  if kind=='extra':(T/'unexpected.txt').write_bytes(b'extra')
  save(T/'manifest.json',m)
  r=subprocess.run(['python3','-B',str(D/'verify.py'),'--payload-only',str(T)],capture_output=True,text=True)
  assert (r.returncode==0)==(kind=='positive')
  results.append({'test':kind,'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
save(D/'negative-test-results.json',results)
files=[rec(p) for p in sorted(D.rglob('*')) if p.is_file() and str(p.relative_to(D)) not in EX]
save(D/'manifest.json',{'excluded_exact_paths':EX,'files':files})
r=subprocess.run(['python3','-B',str(D/'verify.py')],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':rec(D/'manifest.json'),'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'negative_tests':results,'guard':'fixed helper_guard.py; AS/groupRSS512MiB CPU210s wall230s unchanged','scope':'integrity only; no math/novelty PASS'}
save(D/'final-verification-receipt.json',receipt)
print(json.dumps(receipt,indent=2));assert r.returncode==0
