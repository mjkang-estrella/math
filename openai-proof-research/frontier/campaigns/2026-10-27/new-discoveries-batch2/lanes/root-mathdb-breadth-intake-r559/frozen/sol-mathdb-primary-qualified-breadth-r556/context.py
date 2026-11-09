import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;B=L.parent
refs=json.loads((O/'flat-bindings.json').read_text());seen={r['path'] for r in refs}
paths=[B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'sources/upstream.json',B.parents[3]/'sources/CONTENTS.md']
# root research path explicitly
R=next(p for p in O.parents if p.name=='openai-proof-research')
paths += [R/'sources/upstream.json',R/'sources/CONTENTS.md']
for p in paths:
 if p.exists() and str(p) not in seen:
  b=p.read_bytes();refs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()});seen.add(str(p))
(O/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 v=json.loads(p.read_text());print(p.name,str(v)[:9000])
print((R/'sources/upstream.json').read_text())
