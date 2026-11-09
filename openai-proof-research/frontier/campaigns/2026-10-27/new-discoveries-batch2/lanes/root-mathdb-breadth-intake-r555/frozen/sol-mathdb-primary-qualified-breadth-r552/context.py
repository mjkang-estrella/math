import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent
refs=json.loads((P/'flat-bindings.json').read_text())
paths=[L/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]+[L/'root-mathdb-cayley-review-intake-r363/DECISION.md']
for p in paths:
 b=p.read_bytes();refs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for p in paths:print(str(p)+'\n'+p.read_text())
a=json.loads((P/'assigned-records.json').read_text())
for x in a:print(x['mathdb_id'],x['record']['source_url'])
