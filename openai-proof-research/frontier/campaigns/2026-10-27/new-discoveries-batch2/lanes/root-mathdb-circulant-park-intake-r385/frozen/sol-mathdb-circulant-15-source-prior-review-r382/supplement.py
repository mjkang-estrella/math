from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent;L=R.parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
I=L/'root-mathdb-circulant-intake-r375';out=[]
for e in json.loads((I/'bindings.json').read_text()):
 for p in [Path(e['original']),I/e['copy']]:
  assert p.stat().st_size==e['size'] and sha(p)==e['sha256'],str(p)
  out.append({'path':str(p),'sha256':e['sha256'],'size':e['size']})
(R/'supplemental-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'note':'r375 full original/copy binding validation; provenance only, no sibling scientific investigation','files':out},indent=2)+'\n')
print('PASS supplemental',len(out))
