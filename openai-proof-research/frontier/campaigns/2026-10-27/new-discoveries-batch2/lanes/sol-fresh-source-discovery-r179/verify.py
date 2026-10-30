import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),checks=[])
for name in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/name).read_text());expected={r['path'] for r in j['records']}
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(j['exclusions'])
 failures=[]
 if actual!=expected:failures.append(dict(missing=sorted(expected-actual),extra=sorted(actual-expected)))
 for r in j['records']:
  p=L/r['path']
  if not p.is_file() or sha(p.read_bytes())!=r['sha256'] or p.stat().st_size!=r['bytes']:failures.append(r['path'])
 out['checks'].append(dict(target=name,records=len(j['records']),exclusions=j['exclusions'],failures=failures,pass_check=not failures))
g=json.loads((L/'guard-binding.json').read_text());out['guard_unchanged']=sha(Path(g['path']).read_bytes())==g['sha256']
out['pass']=all(x['pass_check'] for x in out['checks']) and out['guard_unchanged']
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2));assert out['pass']
