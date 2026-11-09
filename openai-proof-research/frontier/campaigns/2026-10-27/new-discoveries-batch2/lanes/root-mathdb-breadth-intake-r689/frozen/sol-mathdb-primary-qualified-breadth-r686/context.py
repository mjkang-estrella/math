import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent
paths=[B/'ledger.json',B/'prior-campaign-context.json',L.parent/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L.parent/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L.parent/'root-mathdb-cayley-review-intake-r363/DECISION.md', B.parents[3]/'sources/upstream.json',B.parents[3]/'sources/CONTENTS.md']
a=json.loads((L/'initial-bindings.json').read_text())
for p in paths:
 if p.exists():
  b=p.read_bytes();a.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'initial-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
ids={str(x['record']['mathdb_id']) for x in json.loads((L/'literal-records.json').read_text())}
for p in paths:
 if not p.exists():print('MISSING context path',p);continue
 if p.name=='DECISION.md':print(p.read_text())
 elif p.suffix=='.json':
  v=json.loads(p.read_text());print(p.name,'root',list(v)[:15]);print('assigned id matches',[(i,str(v.get(i))[:400]) for i in ids if isinstance(v,dict) and i in v])
I=L.parent/'root-mathdb-breadth-intake-r685';a=json.loads((I/'active-breadth-reservations.json').read_text());c=json.loads((I/'coverage-delta.json').read_text());assert len(c)==8033
sets=[set(map(str,r['ids'])) for r in a]
for n,s in enumerate(sets):
 assert not s&set(c)
 for t in sets[:n]:assert not s&t
 assert not s&set(map(str,json.loads((I/'reserved-ids-r686.json').read_text())['protected_ids']))
assert ids==set(map(str,json.loads((I/'reserved-ids-r686.json').read_text())['ids']))
print('RESERVATIONS',[(r['lane'],len(r['ids'])) for r in a]);print('count',len(c))
