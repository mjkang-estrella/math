import pathlib,json,hashlib
P=pathlib.Path(__file__).parent;L=P.parent;B=L.parent;repo=B.parents[3]
files=[B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',repo/'sources/upstream.json',repo/'sources/CONTENTS.md',repo/'sources/preprints-tree.json']
refs=json.loads((P/'flat-bindings.json').read_text())
for p in files:
 b=p.read_bytes();refs.append({'path':str(p.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for p in files:
 print('\nCONTEXT',p.name,'\n',p.read_text()[:14000] if p.name not in ['preprints-tree.json','CONTENTS.md','historical-dispositions.json'] else p.read_text()[:1500])
