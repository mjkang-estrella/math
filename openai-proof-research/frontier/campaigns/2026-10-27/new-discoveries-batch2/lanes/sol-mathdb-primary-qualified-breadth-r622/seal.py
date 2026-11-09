import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).parent;guard=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def write(n,x):(P/n).write_text(json.dumps(x,indent=2)+'\n')
def manifest():
 rows=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   b=p.read_bytes();rows.append({'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 write('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':rows})
def run(args):
 r=subprocess.run(['python3','-B',str(guard),'python3','-B',str(P/'verify.py')]+args,capture_output=True,text=True);return {'args':args,'exit':r.returncode,'stdout':r.stdout.strip(),'guard':r.stderr.strip()}
manifest();a=run([]);print(json.dumps(a));assert a['exit']==0
ns=[run(['--negative',s]) for s in ['hash','size','extra']];print(json.dumps(ns));assert all(n['exit']!=0 for n in ns)
write('negative-tests.json',{'mechanism':'In-memory injection into the actual payload checker; no files or originals mutated. Expected manifest hash, size and actual-path set altered independently.','tests':ns})
manifest();a=run([]);assert a['exit']==0,a
b=(P/'manifest.json').read_bytes();write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verification':a,'negative_tests_nonzero':True,'literal_reviews':50,'proposals':0,'integrity_is_not_math_or_novelty_pass':True})
a=run([]);print(json.dumps(a));assert a['exit']==0
print('MANIFEST',hashlib.sha256(b).hexdigest(),len(b))
