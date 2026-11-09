import pathlib,json,hashlib
P=pathlib.Path(__file__).parent;L=P.parent
b=json.loads((P/'flat-bindings.json').read_text())
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:
 p=L/rel;raw=p.read_bytes();e={'sha256':hashlib.sha256(raw).hexdigest(),'size':len(raw)}
 if str(p) in b:assert b[str(p)]==e
 else:b[str(p)]=e
(P/'flat-bindings.json').write_text(json.dumps(b,indent=2,sort_keys=True)+'\n')
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(rel,(L/rel).read_text()[:10000])
for name in ['ledger.json','prior-campaign-context.json']:print(name,(L.parent/name).read_text()[:1800])
