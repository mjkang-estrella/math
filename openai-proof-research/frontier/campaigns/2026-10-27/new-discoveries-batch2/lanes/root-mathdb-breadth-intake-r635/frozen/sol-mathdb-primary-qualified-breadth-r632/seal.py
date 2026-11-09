from pathlib import Path
import json,hashlib,subprocess,sys,datetime
O=Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def j(p):return json.loads(p.read_text())
def put(n,x):(O/n).write_text(json.dumps(x,indent=2)+'\n')
def info(p):
 d=p.read_bytes();return {'path':str(p),'size':len(d),'sha256':hashlib.sha256(d).hexdigest()}
flat=j(O/'flat-bindings.json')
for p in [O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',O.parents[1]/'AGENTS.md']:
 if str(p) not in {e['path'] for e in flat}:flat.append(info(p))
put('flat-bindings.json',flat)
def seal():
 files=[]
 for p in sorted(O.rglob('*')):
  if p.is_file() and str(p.relative_to(O)) not in excluded:
   a=info(p);a['path']=str(p.relative_to(O));files.append(a)
 put('manifest.json',{'excluded_exact_paths':excluded,'files':files})
seal()
neg=[]
for mode,word in [('hash','hash mismatch'),('size','size mismatch'),('extra','extra/missing')]:
 r=subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--negative',mode],capture_output=True,text=True)
 assert r.returncode!=0 and word in r.stdout,(mode,r.stdout,r.stderr)
 neg.append({'mode':mode,'exit':r.returncode,'output':json.loads(r.stdout),'method':'in-memory single mismatch injected into same exact-payload validator; no original or payload mutated'})
put('negative-tests.json',neg);seal()
r=subprocess.run([sys.executable,'-B',str(O/'verify.py')],capture_output=True,text=True);assert r.returncode==0,(r.stdout,r.stderr)
a=info(O/'manifest.json')
put('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':a['sha256'],'manifest_size':a['size'],'result':json.loads(r.stdout),'negative_tests':neg,'guard':'fixed helper_guard.py, unchanged AS/groupRSS512MiB CPU210s wall230s; child verifiers remain in guarded process group','limitations':'Integrity only; no math, priority, full dependency or registry PASS'})
r=subprocess.run([sys.executable,'-B',str(O/'verify.py')],capture_output=True,text=True);assert r.returncode==0,(r.stdout,r.stderr)
print(r.stdout);print(json.dumps(a))
