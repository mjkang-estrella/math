import pathlib,json,hashlib,tempfile,subprocess,datetime
P=pathlib.Path(__file__).parent
def w(n,o):(P/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def ent(p):
 b=p.read_bytes();return {'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
neg=[]
with tempfile.TemporaryDirectory(dir=P,prefix='negative-fixture-') as tmp:
 T=pathlib.Path(tmp);(T/'a').write_bytes(b'x');e={'path':'a','size':1,'sha256':hashlib.sha256(b'x').hexdigest()}
 def run():return subprocess.run(['python3','-B',str(P/'verify.py'),'--payload-only',str(T)],capture_output=True,text=True)
 def manifest(x):(T/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json'],'files':[x]}))
 manifest(e);assert run().returncode==0
 for typ in ['hash','size','extra-file']:
  x=dict(e)
  if typ=='hash':x['sha256']='0'*64
  if typ=='size':x['size']=2
  if typ=='extra-file':(T/'unexpected').write_bytes(b'!')
  manifest(x);r=run();assert r.returncode!=0;neg.append({'mutation':typ,'exit':r.returncode,'stderr':r.stderr.strip(),'originals_mutated':False})
w('negative-tests.json',neg)
w('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[ent(p) for p in sorted(P.rglob('*')) if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}]})
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
w('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':ent(P/'manifest.json'),'read_only_verifier_result':json.loads(r.stdout),'negative_tests_rejected':3,'resource_guard':'512MiB AS/groupRSS CPU210s wall230s unchanged','scientific_gate':'HOLD; integrity does not certify mathematics, novelty or eligibility'})
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr;print(r.stdout);print(json.dumps(ent(P/'manifest.json')))
