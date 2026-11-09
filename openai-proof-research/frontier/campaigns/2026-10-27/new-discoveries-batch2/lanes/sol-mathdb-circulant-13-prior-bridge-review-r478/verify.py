"""Read-only validation of payloads/references; only receipt is written locally."""
import pathlib,json,hashlib,sys,datetime
O=pathlib.Path(__file__).resolve().parent
EXCLUDED={'manifest.json','final-receipt.json'}
def verify():
 m=json.loads((O/'manifest.json').read_text())
 expected={r['path'] for r in m['files']}
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in EXCLUDED}
 if actual!=expected:raise ValueError('payload set mismatch: '+repr(actual^expected))
 def check(p,r):
  b=p.read_bytes()
  if len(b)!=r['size'] or hashlib.sha256(b).hexdigest()!=r['sha256']:raise ValueError('hash/size mismatch: '+str(p))
 for r in m['files']:check(O/r['path'],r)
 refs=0
 for name in ['input-bindings.json','additional-bindings.json']:
  for r in json.loads((O/name).read_text()):check(pathlib.Path(r['path']),r);refs+=1
 return {'status':'PASS','payloads':len(expected),'flat_references':refs,'manifest_sha256':hashlib.sha256((O/'manifest.json').read_bytes()).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Integrity only; no mathematical/novelty clearance'}
try:
 r=verify();code=0
except Exception as e:
 r={'status':'FAIL','error':str(e)};code=1
(O/'final-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));sys.exit(code)
