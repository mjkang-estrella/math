import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def check(rows,root):
 failures=[]
 for p,h,z in rows:
  f=root/p;b=f.read_bytes() if f.is_file() else b''
  if not f.is_file() or hashlib.sha256(b).hexdigest()!=h or len(b)!=z:failures.append(p)
 return failures
mode=sys.argv[1]
if mode=='science':
 j=json.loads((L/'scientific-freeze.json').read_text());bad=check(j['local'],L)+check(j['originals'],Path('/'))
 out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not bad else 'FAIL',local_records=len(j['local']),original_records=len(j['originals']),failures=bad,exclusions=j['exclusions'])
 name='scientific-verification.json'
else:
 j=json.loads((L/'finalmanifest.json').read_text());bad=check(j['records'],L)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()};expected={r[0] for r in j['records']}|set(j['exclusions'])
 extra=sorted(actual-expected)
 out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not bad and not extra else 'FAIL',manifest_sha256=hashlib.sha256((L/'finalmanifest.json').read_bytes()).hexdigest(),records=len(j['records']),failures=bad,extra=extra,exclusions=j['exclusions'])
 name='manifest-verification.json'
(L/name).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));assert out['status']=='PASS'
