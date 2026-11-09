import pathlib,json,hashlib,datetime,subprocess,sys,tempfile
P=pathlib.Path(__file__).parent

def h(b):return hashlib.sha256(b).hexdigest()
def w(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
# Only tiny fixtures; no original or delivered payload mutation.
neg=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=P) as td:
 t=pathlib.Path(td);(t/'a').write_bytes(b'abc');m={'excluded_exact_paths':['manifest.json'],'files':[{'path':'a','size':3,'sha256':h(b'abc')}]};(t/'manifest.json').write_text(json.dumps(m))
 def run():return subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--payload-only',str(t)],capture_output=True,text=True)
 assert run().returncode==0
 for typ,b,extra in [('hash',b'abd',False),('size',b'abcd',False),('extra-file',b'abc',True)]:
  (t/'a').write_bytes(b)
  if extra:(t/'extra').write_text('unexpected')
  r=run();assert r.returncode!=0;neg.append({'test':typ,'exit_code':r.returncode,'stderr':r.stderr.strip()})
w('negative-tests.json',{'tests':neg,'originals_mutated':False,'fixture_removed':True})
files=[]
for f in sorted(P.rglob('*')):
 if f.is_file() and f.name not in ['manifest.json','final-verification-receipt.json']:
  b=f.read_bytes();files.append({'path':str(f.relative_to(P)),'size':len(b),'sha256':h(b)})
w('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True);print(r.stdout,r.stderr);assert r.returncode==0
b=(P/'manifest.json').read_bytes();w('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(b),'manifest_size':len(b),'verification':json.loads(r.stdout),'negative_tests':neg,'verifier_read_only':True,'guard':'fixed512MiB AS/groupRSS CPU210s wall230s, all Python under helper_guard','acceptance_gate':'INTEGRITY_ONLY; mathematical completeness and novelty not PASS'})
print('MANIFEST',h(b),len(b),'payload_files',len(files))
