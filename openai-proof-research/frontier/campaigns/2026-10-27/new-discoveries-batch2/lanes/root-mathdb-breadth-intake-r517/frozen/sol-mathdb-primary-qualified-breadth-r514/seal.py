import json,pathlib,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
EX=['manifest.json','final-verification-receipt.json']
def h(b):return hashlib.sha256(b).hexdigest()
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
b=json.loads((P/'flat-bindings.json').read_text());guard=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
if str(guard) not in {e['path'] for e in b}:
 a=guard.read_bytes();b.append(dict(path=str(guard),size=len(a),sha256=h(a)));write('flat-bindings.json',b)
def seal():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in EX:
   b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),size=len(b),sha256=h(b)))
 write('manifest.json',dict(excluded_exact_paths=EX,files=files))
seal();results=[]
for mode,message in [('--negative-hash','hash '),('--negative-size','size '),('--negative-extra','extra/missing payload')]:
 r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),mode],capture_output=True,text=True,timeout=25)
 assert r.returncode==1 and message in r.stderr and 'UNEXPECTEDLY' not in r.stderr,(mode,r.stdout,r.stderr)
 results.append(dict(mode=mode,exit=r.returncode,stderr=r.stderr,method='in-memory expected hash/size or actual-name-set perturbation; no files mutated'))
write('negative-tests.json',results);seal()
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True,timeout=35)
assert r.returncode==0,(r.stdout,r.stderr)
b=(P/'manifest.json').read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(b),manifest_size=len(b),exit=r.returncode,verification=json.loads(r.stdout),negative_tests=results,resource_execution='fixed guard; 512MiB AS/groupRSS CPU210 wall230 unchanged',evidence_limit='Integrity only; no mathematical/novelty PASS')
write('final-verification-receipt.json',receipt);print(json.dumps(receipt))
