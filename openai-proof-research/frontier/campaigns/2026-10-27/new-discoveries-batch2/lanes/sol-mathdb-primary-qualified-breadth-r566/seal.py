import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def h(b):return hashlib.sha256(b).hexdigest()
def write(n,o):(P/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def seal():
 entries=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in excluded:
   b=p.read_bytes();entries.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':h(b)})
 write('manifest.json',{'excluded_exact_paths':excluded,'files':entries})
assert not (P/'final-verification-receipt.json').exists(),'Do not reseal an already finalized lane'
seal();tests=[]
for mode in ['hash','size','extra']:
 p=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--negative',mode],capture_output=True,text=True)
 tests.append({'injection':mode,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'original_files_mutated':False})
 assert p.returncode!=0 and {'hash':'HASH','size':'SIZE','extra':'EXTRA/MISSING'}[mode] in p.stderr
write('negative-test-results.json',{'method':'In-memory byte/name fault injection through actual payload validator; actual originals read and unchanged. Each invocation must exit nonzero.','tests':tests})
seal()
p=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
assert p.returncode==0,p.stderr
b=(P/'manifest.json').read_bytes();r=json.loads(p.stdout)
write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':{'size':len(b),'sha256':h(b)},'independent_verifier':r,'negative_tests':3,'negative_hash_size_extra_rejected':True,'guard':'fixed helper_guard.py; AS/groupRSS512MiB CPU210s wall230s; unchanged; parent guard covers all subprocesses','command':'OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py','acceptance':'Integrity only. Mathematical, full-dependency, source/prior and registry acceptance not cleared.'})
p=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True);assert p.returncode==0,p.stderr
print(p.stdout);print('manifest',len(b),h(b))
