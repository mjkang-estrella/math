import pathlib,json,hashlib,subprocess,tempfile,shutil,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;guard=L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def entry(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
refs=json.loads((P/'flat-bindings.json').read_text());mapping={e['path']:e for e in refs}
for p in [guard,P.parents[5]/'AGENTS.md',L.parent/'AGENTS.md']:
 if p.exists():mapping[str(p)]=entry(p)
(P/'flat-bindings.json').write_text(json.dumps(list(mapping.values()),indent=2)+'\n')
def seal():
 files=[]
 for p in sorted(P.rglob('*')):
  if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
   e=entry(p);e['path']=str(p.relative_to(P));files.append(e)
 (P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
(P/'negative-test-results.json').write_text('[]\n');seal();results=[]
# Copy only this small lane payload, never corpus/history; delete temporary copies.
for kind in ['hash','size','extra-file']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as td:
  T=pathlib.Path(td)/'payload';T.mkdir()
  for p in P.iterdir():
   if p.is_file():shutil.copyfile(p,T/p.name)
  target=T/'proposals.json'
  if kind=='hash':target.write_bytes(b'{}\n')
  elif kind=='size':target.write_bytes(b'[]\n ')
  else:(T/'unexpected.txt').write_text('negative fixture')
  run=subprocess.run(['python3','-B',str(P/'verify.py'),str(T)],capture_output=True,text=True)
  expected={'hash':'hash mismatch','size':'size mismatch','extra-file':'exact payload mismatch'}[kind]
  assert run.returncode!=0 and expected in run.stderr,(kind,run.stdout,run.stderr)
  results.append({'case':kind,'exit':run.returncode,'expected_rejection':expected,'stderr':run.stderr})
(P/'negative-test-results.json').write_text(json.dumps(results,indent=2)+'\n');seal()
run=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=entry(P/'manifest.json');receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':m['sha256'],'manifest_size':m['size'],'verifier_sha256':entry(P/'verify.py')['sha256'],'command':'OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B '+str(guard)+' python3 -B '+str(P/'verify.py'),'verification':json.loads(run.stdout),'negative_tests':'hash/size/extra-file rejected; originals never mutated','upstream_verify_executed':False}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
