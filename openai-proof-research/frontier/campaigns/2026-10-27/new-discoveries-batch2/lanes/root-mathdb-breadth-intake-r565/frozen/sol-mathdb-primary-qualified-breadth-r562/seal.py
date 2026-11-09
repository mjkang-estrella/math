import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def write(n,o):(P/n).write_text(json.dumps(o,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def rec(p):
 b=p.read_bytes();return {'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def manifest():write('manifest.json',{'excluded_exact_paths':excluded,'files':[rec(p) for p in sorted(P.rglob('*')) if p.is_file() and str(p.relative_to(P)) not in excluded]})
manifest();tests=[]
for mode in ['--negative-hash','--negative-size','--negative-extra']:
 r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),mode],capture_output=True,text=True)
 tests.append({'mode':mode,'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'method':'in-memory virtual perturbation through same production hash/size/exact-payload checks; no originals or payload mutated'})
 assert r.returncode!=0,(mode,'accepted')
write('negative-test-results.json',tests);manifest()
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'verification':json.loads(r.stdout),'negative_rejections':tests,'scientific_gates':'HOLD; integrity is administrative only','deviations':'See failures.md; no retroactive timing clearance'};write('final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2))
