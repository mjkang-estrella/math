from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
p=L/'finalmanifest.json';j=json.loads(p.read_bytes())
for x in j['files']:
 q=L/x['path'];assert q.is_file();b=q.read_bytes()
 assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'],x['path']
expected={x['path'] for x in j['files']}
actual={str(q.relative_to(L)) for q in L.rglob('*') if q.is_file() and q.name not in j['excluded']}
assert expected==actual,(expected-actual,actual-expected)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',verified_paths=len(expected),manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='All included files size/hash and complete file-set equality; excludes manifest/verification receipt/logs as declared.')
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
