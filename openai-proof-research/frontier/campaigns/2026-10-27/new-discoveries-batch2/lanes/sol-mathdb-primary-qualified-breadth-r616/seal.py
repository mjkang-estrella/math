import pathlib,json,hashlib,subprocess,datetime,os
P=pathlib.Path(__file__).resolve().parent
assert os.environ['OPENBLAS_NUM_THREADS']==os.environ['OMP_NUM_THREADS']=='1'
def entry(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def seal():
 fs=[{'path':str(p.relative_to(P)),**entry(p)} for p in sorted(P.rglob('*')) if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']]
 (P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':fs},indent=2)+'\n')
seal();neg=[]
for mode in ['hash','size','extra']:
 r=subprocess.run(['python3','-B',str(P/'verify.py'),'--fault',mode],capture_output=True,text=True);assert r.returncode!=0
 neg.append({'fault':mode,'mutation':'in-memory only; no originals changed','exit':r.returncode,'stderr':r.stderr.strip()})
(P/'negative-tests.json').write_text(json.dumps(neg,indent=2)+'\n');seal()
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':entry(P/'manifest.json'),'verifier':entry(P/'verify.py'),'verification_exit':r.returncode,'result':json.loads(r.stdout),'negative_tests':neg,'guard':'512MiB AS/groupRSS, CPU210s, wall230s unchanged; run under fixed helper_guard.py','integrity_is_not_math_or_novelty_pass':True}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
