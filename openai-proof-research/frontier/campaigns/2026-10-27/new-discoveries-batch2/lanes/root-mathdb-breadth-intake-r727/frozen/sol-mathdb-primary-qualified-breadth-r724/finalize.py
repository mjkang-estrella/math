import pathlib,json,hashlib,datetime,importlib.util,tempfile,copy
P=pathlib.Path(__file__).resolve().parent;L=P.parent
j=lambda p:json.loads(p.read_text())
def bind(p):
 b=p.read_bytes();return {'path':str(p.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
refs=j(P/'flat-bindings.json')
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md',L/'sol-mathdb-primary-qualified-breadth-r684/failures.json',L/'sol-mathdb-primary-qualified-breadth-r642/failures.md',L/'sol-mathdb-primary-qualified-breadth-r642/source-provenance.json']:
 if p.exists() and str(p.resolve()) not in {e['path'] for e in refs}:refs.append(bind(p))
write('flat-bindings.json',refs)
# Test the actual verifier primitives with a small synthetic fixture entirely inside this lane.
spec=importlib.util.spec_from_file_location('independent_verifier',P/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
neg={}
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=P) as td:
 root=pathlib.Path(td);f=root/'sample';f.write_bytes(b'bounded fixture\n');e=bind(f);e['path']='sample';m={'excluded_exact_paths':[],'files':[e]};v.exact(root,m)
 for kind in ['hash','size','extra_file']:
  mutated=copy.deepcopy(m)
  if kind=='hash':mutated['files'][0]['sha256']='0'*64
  if kind=='size':mutated['files'][0]['size']+=1
  if kind=='extra_file':(root/'unexpected').write_bytes(b'x')
  try:v.exact(root,mutated)
  except ValueError as err:neg[kind]={'rejected':True,'message':str(err)}
  else:raise AssertionError('negative accepted '+kind)
write('negative-tests.json',{'fixture':'temporary bounded own-lane directory, removed; actual verifier primitives; no original mutation','tests':neg})
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  r=bind(p);r['path']=str(p.relative_to(P));files.append(r)
write('manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files})
result=v.verify();write('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':bind(P/'manifest.json'),'verification':result,'negative_tests':neg,'guard':'512MiB AS/groupRSS, CPU210s,wall230s unchanged; all Python invoked through fixed guard','read_only_verifier':'verify.py; no upstream verify.py executed'})
print(json.dumps(j(P/'final-verification-receipt.json'),indent=2))
