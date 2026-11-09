from pathlib import Path
import json,hashlib
D=Path(__file__).parent;L=D.parent;B=L.parent
ps=[B/'ledger.json',B/'prior-campaign-context.json',L.parents[4]/'sources/upstream.json']
ps += list((L/'root-mathdb-accepted-exclusions-r304').glob('*.json'))+list((L/'root-mathdb-cayley-review-intake-r363').glob('*'))
repo=next(x for x in D.parents if x.name=='openai-proof-research');ps +=[repo/'sources/upstream.json',repo/'sources/CONTENTS.md']
b=json.loads((D/'flat-bindings.json').read_text())
for p in ps:
 if p.is_file():
  raw=p.read_bytes();b.append(dict(path=str(p.resolve()),size=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
(D/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
for p in ps:
 if p.is_file():
  raw=p.read_text();print(str(p),raw[:1800] if p.suffix!='.json' or p.name in ['upstream.json','prior-campaign-context.json'] else 'bound and parsed; keys '+str(list(json.loads(raw))[:20]))
