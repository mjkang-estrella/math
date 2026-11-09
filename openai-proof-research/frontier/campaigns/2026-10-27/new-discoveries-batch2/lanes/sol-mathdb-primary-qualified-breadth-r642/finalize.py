import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
def write(n,x):(P/n).write_text(json.dumps(x,indent=2)+'\n')
def manifest():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}:
   b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':h(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
# Preliminary complete manifest, virtual mutation probes alter only expectations/inventory.
write('negative-tests.json',[]);manifest();results=[]
for kind in ['hash','size','extra']:
 r=subprocess.run(['python3','-B',str(P/'verify.py'),'--negative',kind],capture_output=True,text=True)
 results.append({'test':kind,'exit_code':r.returncode,'stderr':r.stderr.strip(),'method':'virtual expectation/inventory mutation; original files unchanged'})
 assert r.returncode!=0
write('negative-tests.json',results);manifest()
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
b=(P/'manifest.json').read_bytes()
write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':{'size':len(b),'sha256':h(b)},'verification':json.loads(r.stdout),'negative_tests':results,'guard':'unchanged fixed helper_guard.py: AS/groupRSS512MiB CPU210s wall230s; python3 -B; thread env1','scientific_acceptance':False})
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
print(r.stdout.strip());print('manifest',len(b),h(b))
