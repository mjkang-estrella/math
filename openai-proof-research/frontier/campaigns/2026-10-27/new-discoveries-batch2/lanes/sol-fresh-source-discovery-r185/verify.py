import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
for inp,out in [('scientific-freeze.json','scientific-verification.json'),('finalmanifest.json','manifest-verification.json')]:
 raw=(L/inp).read_bytes();j=json.loads(raw);bad=[]
 for r in j['records']:
  p=L/r['path']
  if not p.is_file() or sha(p.read_bytes())!=r['sha256'] or p.stat().st_size!=r['bytes']:bad.append(r['path'])
 expected={r['path'] for r in j['records']};actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in j['exclusions']}
 extra=sorted(actual-expected);missing=sorted(expected-actual)
 receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),input=inp,input_sha256=sha(raw),checked=len(expected),bad=bad,extra=extra,missing=missing,pass_all=not(bad or extra or missing),explicit_exclusions=j['exclusions'])
 (L/out).write_text(json.dumps(receipt,indent=2)+'\n');assert receipt['pass_all'],receipt
 print(inp,'PASS',len(expected))
