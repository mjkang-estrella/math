from pathlib import Path
import json,hashlib,datetime,subprocess,tempfile,shutil
P=Path(__file__).resolve().parent
def h(b):return hashlib.sha256(b).hexdigest()
def write(n,x):(P/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def manifest():
 excluded={'manifest.json','final-verification-receipt.json'}
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in excluded:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':h(b)})
 write('manifest.json',{'excluded_exact_paths':sorted(excluded),'receipt_name':'final-verification-receipt.json','files':files})
manifest()
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
negative=[]
# Only this lane's small payload is copied; never upstream originals or corpus.
for kind in ['hash','size','extra-file']:
 with tempfile.TemporaryDirectory(prefix='.negative-',dir=P) as td:
  Q=Path(td)
  for p in list(P.iterdir()):
   if p.is_file() and p.name!='final-verification-receipt.json':shutil.copyfile(p,Q/p.name)
  if kind=='hash':
   p=Q/'proposals.json';b=p.read_bytes();p.write_bytes(b'{}'+b[2:])
  if kind=='size':
   with (Q/'proposals.json').open('ab') as f:f.write(b' ')
  if kind=='extra-file':(Q/'unexpected.txt').write_text('negative fixture')
  t=subprocess.run(['python3','-B',str(P/'verify.py'),str(Q)],capture_output=True,text=True)
  assert t.returncode!=0,(kind,t.stdout,t.stderr)
  negative.append({'mutation':kind,'exit':t.returncode,'diagnostic':t.stderr.strip(),'originals_mutated':False})
write('negative-tests.json',negative)
manifest()
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
b=(P/'manifest.json').read_bytes()
write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(b),'manifest_size':len(b),'verifier_exit':r.returncode,'verifier_result':json.loads(r.stdout),'negative_tests':negative,'math_novelty_pass':False,'guard':'512MiB AS/groupRSS CPU210s wall230s unchanged; invoked through fixed helper_guard.py'})
print((P/'final-verification-receipt.json').read_text())
