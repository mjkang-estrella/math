"""Read-only identity verification; not a mathematical verdict. MIT."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,sys
R=Path(__file__).resolve().parent;W=R.parents[4]
def check():
 p=argparse.ArgumentParser();p.add_argument('--manifest-sha256',required=True);a=p.parse_args()
 raw=(R/'output-manifest.json').read_bytes()
 if hashlib.sha256(raw).hexdigest()!=a.manifest_sha256:raise ValueError('external manifest anchor mismatch')
 records=json.loads(raw)['files']; expected={'output-manifest.json'}
 for e in records:
  n=e['path']; pp=PurePosixPath(n)
  if pp.is_absolute() or '..' in pp.parts or str(pp)!=n or n in expected:raise ValueError('invalid member')
  expected.add(n);f=R/n
  if f.is_symlink():raise ValueError('linked member')
  d=f.read_bytes()
  if len(d)!=e['bytes'] or hashlib.sha256(d).hexdigest()!=e['sha256']:raise ValueError('changed review file '+n)
 actual={f.relative_to(R).as_posix() for f in R.rglob('*') if f.is_file() and 'tmp' not in f.relative_to(R).parts}
 if actual!=expected:raise ValueError('review membership mismatch')
 inputs=json.loads((R/'fixed-inputs.json').read_text())
 for n,e in inputs.items():
  d=(W/n).read_bytes()
  if len(d)!=e['bytes'] or hashlib.sha256(d).hexdigest()!=e['sha256']:raise ValueError('changed fixed input '+n)
 print(json.dumps({'status':'REVIEW_IDENTITY_ONLY','review_payloads':len(records),'fixed_inputs':len(inputs),'writes':0}))
if __name__=='__main__':
 try:check()
 except Exception as exc:print('REJECT: '+str(exc),file=sys.stderr);sys.exit(1)
