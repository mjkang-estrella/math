import pathlib,json,hashlib,importlib.util,tempfile,datetime,subprocess
O=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('independent',O/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
results=[]
# Small isolated fixtures, never mutate originals or copy corpus/history.
with tempfile.TemporaryDirectory(prefix='negative-',dir=O) as t:
 p=pathlib.Path(t);(p/'x').write_bytes(b'ab');good={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'x','size':2,'sha256':hashlib.sha256(b'ab').hexdigest()}]}
 v.payload(p,good)
 for mode in ['hash','size','extra-file']:
  m=json.loads(json.dumps(good))
  if mode=='hash':m['files'][0]['sha256']='0'*64
  elif mode=='size':m['files'][0]['size']=3
  else:(p/'extra').write_bytes(b'x')
  try:v.payload(p,m)
  except v.Mismatch as e:results.append({'test':mode,'rejected':True,'reason':str(e)})
  else:raise AssertionError('negative accepted')
(O/'negative-tests.json').write_text(json.dumps({'method':'Independent verifier payload function on bounded isolated fixtures; same function verifies actual payload. Originals unchanged.','results':results},indent=2)+'\n')
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  d=p.read_bytes();files.append({'path':str(p.relative_to(O)),'size':len(d),'sha256':hashlib.sha256(d).hexdigest()})
m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files};(O/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
# The verifier is read-only; receipt is generated here, not by verifier.
r=v.main();d=(O/'manifest.json').read_bytes();r.update({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':{'sha256':hashlib.sha256(d).hexdigest(),'size':len(d)},'negative_tests':results,'payload_files':len(files)})
(O/'final-verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
