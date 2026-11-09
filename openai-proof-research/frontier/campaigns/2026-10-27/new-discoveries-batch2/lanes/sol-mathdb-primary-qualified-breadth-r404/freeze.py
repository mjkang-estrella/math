from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent; B=L.parent
refs={}
def bind(p):
 p=p.resolve(); b=p.read_bytes(); refs[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
for d in ['root-mathdb-breadth-intake-r403','root-mathdb-accepted-exclusions-r304']:
 for p in (B/d).rglob('*'):
  if p.is_file():bind(p)
for p in [B/'pi-mathdb-full-corpus-inventory-r301/manifest.json',B/'root-mathdb-cayley-review-intake-r363/disposition.json']:
 bind(p)
(L/'bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'phase':'pre-content flat immutable references','refs':refs},indent=2)+'\n')
print('bound',len(refs))
