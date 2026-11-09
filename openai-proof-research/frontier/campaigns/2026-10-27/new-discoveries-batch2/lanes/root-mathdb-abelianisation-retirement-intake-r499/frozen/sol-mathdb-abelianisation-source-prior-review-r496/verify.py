from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent
EXCLUDED={'manifest.json','final-receipt.json'}
def check_bytes(b,e):
 if len(b)!=e['size'] or hashlib.sha256(b).hexdigest()!=e['sha256']:raise ValueError('bytes/size mismatch: '+e['path'])
def verify():
 m=json.loads((D/'manifest.json').read_text());assert set(m['excluded_exact_paths'])==EXCLUDED
 seen=set()
 for e in m['files']:
  p=Path(e['path']);assert not p.is_absolute() and '..' not in p.parts and str(p) not in seen
  seen.add(str(p));assert (D/p).resolve().is_relative_to(D);check_bytes((D/p).read_bytes(),e)
 assert seen=={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()}-EXCLUDED
 flat=json.loads((D/'flat-original-bindings.json').read_text())
 for row in flat:
  for kind in ['original','intake_copy','retained']:
   e=row[kind];check_bytes(Path(e['path']).read_bytes(),e)
 for e in json.loads((D/'input-bindings.json').read_text()):check_bytes(Path(e['path']).read_bytes(),e)
 for e in m['files']:
  b=(D/e['path']).read_bytes();mut=b+b'X'
  try:check_bytes(mut,e)
  except ValueError:pass
  else:raise AssertionError('mutation accepted')
 return len(seen)
if __name__=='__main__':
 n=verify();receipt={'status':'PASS','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'payloads':n,'manifest_sha256':hashlib.sha256((D/'manifest.json').read_bytes()).hexdigest(),'self_test':'Each payload mutated in memory and rejected','flat_bindings':'all original/intake/retained copies rehashed','input_bindings':'rehash PASS','meaning':'Integrity only; not math/novelty/acceptance','counts':{'additional':9,'total':39,'next':40}}
 (D/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
