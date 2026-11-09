from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;M=L.parents[5];C=L.parent.parent
paths=[C/'ledger.json',C/'prior-campaign-context.json',M/'sources/upstream.json',M/'sources/CONTENTS.md']
refs=[]
for p in paths:
 b=p.read_bytes();refs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'context-bindings.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':refs},indent=2)+'\n')
for p in paths:
 s=p.read_text();print(p.name, s[:4500] if p.name!='CONTENTS.md' else s[:900])
