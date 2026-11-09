import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
G=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def write(n,o):(P/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def seal():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
seal()
neg=[]
for mode in ['hash','size','extra']:
 r=subprocess.run(['python3','-B',str(P/'verify.py'),mode],capture_output=True,text=True)
 assert r.returncode!=0
 neg.append({'mode':mode,'returncode':r.returncode,'stderr':r.stderr,'method':'Read-only expected hash/size or observed file-set injection; original files unchanged'})
write('negative-test-results.json',neg);seal()
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
receipt=json.loads(r.stdout);receipt.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),negative_tests_rejected=3,guard='All seal/verification subprocesses inside unchanged helper_guard process group: AS/groupRSS512MiB CPU210s wall230s',read_only_verifier=True)
write('final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2))
