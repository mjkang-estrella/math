import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def write(n,x):(P/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def ent(p):
 b=p.read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def seal():write('manifest.json',{'excluded_exact_paths':sorted(EX),'files':[dict(path=str(p.relative_to(P)),**ent(p)) for p in sorted(P.rglob('*')) if p.is_file() and str(p.relative_to(P)) not in EX]})
seal();tests=[]
for mode in ['hash','size','extra']:
 r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--negative',mode],capture_output=True,text=True);assert r.returncode!=0
 tests.append({'test':mode,'injected':'in-memory only; no original mutation','exit_code':r.returncode,'stderr':r.stderr.strip()})
write('negative-tests.json',{'all_rejected':True,'tests':tests});seal()
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':ent(P/'manifest.json'),'verifier':ent(P/'verify.py'),'result':json.loads(r.stdout),'exit_code':r.returncode,'negative_tests_passed':True,'guard':'unchanged helper_guard.py; AS/groupRSS512MiB CPU210s wall230s','interpretation':'Integrity only; no mathematical or novelty PASS'})
print((P/'final-verification-receipt.json').read_text())
