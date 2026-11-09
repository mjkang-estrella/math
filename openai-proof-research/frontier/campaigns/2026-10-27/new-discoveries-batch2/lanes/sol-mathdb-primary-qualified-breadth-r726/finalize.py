import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def write(n,x):(P/n).write_text(json.dumps(x,indent=2)+'\n')
def manifest():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and str(p.relative_to(P)) not in excluded:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 write('manifest.json',{'excluded_exact_paths':excluded,'files':files})
manifest();neg=[]
for mode in ['hash','size','extra']:
 p=subprocess.run([str(P/'verify.sh'),'--negative='+mode],capture_output=True,text=True)
 assert p.returncode!=0,(mode,p.stdout,p.stderr)
 neg.append({'fault':mode,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'originals_mutated':False,'method':'in-memory injection into the same read-only verifier check path'})
write('negative-tests.json',neg);manifest()
p=subprocess.run([str(P/'verify.sh')],capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':p.returncode,'verifier_stdout':p.stdout,'guard_stderr':p.stderr,'negative_rejections':3,'integrity':'PASS','mathematics_and_novelty':'HOLD','accepted_credit':0}
write('final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2))
