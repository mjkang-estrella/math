import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
EX=['manifest.json','final-verification-receipt.json']
def write(n,x):(P/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def manifest():
 entries=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in EX:
   b=p.read_bytes();entries.append(dict(path=str(p.relative_to(P)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
 write('manifest.json',dict(excluded_exact_paths=EX,files=entries))
write('negative-tests.json',dict(status='pending'));manifest();tests=[]
for mode in ['hash','size','extra']:
 r=subprocess.run(['python3','-B',str(P/'verify.py'),'--negative='+mode],capture_output=True,text=True);assert r.returncode!=0;assert {'hash':'hash mismatch','size':'size mismatch','extra':'extra/missing file'}[mode] in r.stderr;tests.append(dict(mode=mode,exit_code=r.returncode,stderr=r.stderr.strip(),scope='In-memory injection through identical exact-payload checker; no files mutated'))
write('negative-tests.json',dict(status='PASS',tests=tests));manifest()
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
b=(P/'manifest.json').read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),verification=json.loads(r.stdout),negative_tests='PASS',guard='Fixed helper_guard.py; AS/groupRSS512MiB CPU210s wall230s unchanged',integrity_is_not_math_or_novelty_PASS=True)
write('final-verification-receipt.json',receipt);print(json.dumps(receipt))
