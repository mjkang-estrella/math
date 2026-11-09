from pathlib import Path
import json,hashlib,datetime
from verify import verify
D=Path(__file__).resolve().parent
# Add final flat support-file bindings, without changing any originals.
b=json.loads((D/'flat-bindings.json').read_text());known={r['path'] for r in b}
for p in [D.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',D.parents[5]/'AGENTS.md',D.parent.parent/'AGENTS.md']:
 if p.exists() and str(p) not in known:
  v=p.read_bytes();b.append({'path':str(p),'sha256':hashlib.sha256(v).hexdigest(),'size':len(v)})
(D/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
entries=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  v=p.read_bytes();entries.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(v).hexdigest(),'size':len(v)})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':entries},indent=2)+'\n')
r=verify();r['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();r['negative_tests']=json.loads((D/'negative-tests.json').read_text())
(D/'final-verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
