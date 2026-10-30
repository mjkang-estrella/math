import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
for name,out in [('scientific-freeze.json','scientific-verification.json'),('finalmanifest.json','manifest-verification.json')]:
 j=json.loads((L/name).read_text());bad=[]
 for r in j['records']:
  p=L/r['path']
  if not p.is_file() or len(p.read_bytes())!=r['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=r['sha256']:bad.append(r['path'])
 expected={r['path'] for r in j['records']}
 actual={p.relative_to(L).as_posix() for p in L.rglob('*') if p.is_file() and p.relative_to(L).as_posix() not in j['exclusions']}
 assert not bad and actual==expected,(bad,actual^expected)
 rec=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified=name,sha256=hashlib.sha256((L/name).read_bytes()).hexdigest(),records=len(expected),bad=bad,inventory_exact=True,exclusions=j['exclusions'],status='PASS')
 (L/out).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
