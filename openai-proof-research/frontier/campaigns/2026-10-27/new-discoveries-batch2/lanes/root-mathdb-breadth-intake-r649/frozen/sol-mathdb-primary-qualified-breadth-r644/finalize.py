import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(n,x):(P/n).write_text(json.dumps(x,indent=2)+'\n')
def manifest():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),size=len(b),sha256=sha(b)))
 put('manifest.json',dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=files))
manifest()
neg=[]
for fault in ['hash','size','extra']:
 p=subprocess.run(['python3','-B',str(P/'verify.py'),'--fault',fault],capture_output=True,text=True);assert p.returncode!=0
 neg.append(dict(fault=fault,exit=p.returncode,stderr=p.stderr.strip(),method='in-memory payload bytes/name mutation; no original or payload edited'))
put('negative-tests.json',neg);manifest()
p=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True)
b=(P/'manifest.json').read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(b),manifest_size=len(b),verification_exit=p.returncode,stdout=p.stdout,stderr=p.stderr,negative_rejections=3,math_novelty='NOT_CERTIFIED',current_registry='HOLD')
put('final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2));assert p.returncode==0
