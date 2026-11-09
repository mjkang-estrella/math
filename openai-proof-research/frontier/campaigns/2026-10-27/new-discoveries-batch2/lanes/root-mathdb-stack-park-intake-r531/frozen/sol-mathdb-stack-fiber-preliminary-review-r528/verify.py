"""Read-only hash/size/exact-file-set checker; never evaluates mathematics."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
EX={'manifest.json','finalreceipt.json'}
def check():
 m=json.loads((D/'manifest.json').read_bytes());assert set(m['excluded_exact_paths'])==EX
 expected={x['path']:x for x in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()}-EX
 mode=sys.argv[1] if len(sys.argv)>1 else ''
 if mode=='--negative-extra':actual.add('in-memory-extra.bin')
 if mode in ['--negative-hash','--negative-size']:
  x=expected[sorted(expected)[0]]
  if mode=='--negative-hash':x['sha256']='0'*64
  else:x['size']+=1
 assert actual==set(expected), 'extra/missing payload'
 for name,x in expected.items():
  p=D/name;assert not p.is_symlink();b=p.read_bytes()
  assert len(b)==x['size'], 'size mismatch: '+name
  assert hashlib.sha256(b).hexdigest()==x['sha256'], 'hash mismatch: '+name
 for x in json.loads((D/'flat-bindings.json').read_bytes()):
  b=Path(x['path']).read_bytes()
  assert len(b)==x['size'] and hashlib.sha256(b).hexdigest()==x['sha256'], 'external mismatch: '+x['path']
 print(json.dumps(dict(ok=True,payloads=len(expected),external_references=len(json.loads((D/'flat-bindings.json').read_bytes())))))
try:check()
except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
