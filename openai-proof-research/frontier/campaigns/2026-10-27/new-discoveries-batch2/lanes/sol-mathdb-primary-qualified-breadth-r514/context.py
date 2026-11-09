import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;R=B.parents[3]
b=json.loads((P/'flat-bindings.json').read_text())
for p in [R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']:
 if p.exists():
  a=p.read_bytes();b.append(dict(path=str(p),size=len(a),sha256=hashlib.sha256(a).hexdigest()))
(P/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
ids={r['mathdb_id'] for r in json.loads((P/'assigned-records.json').read_text())}
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((B/n).read_text());print(n,'keys',list(d) if isinstance(d,dict) else len(d));print(json.dumps(d,ensure_ascii=False)[:1500])
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 d=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,'keys',list(d));
 # Read complete structure, expose matched contexts and all family scopes for independent comparison.
 if n.startswith('accepted'):
  for f in d.get('families',[]):print(f.get('number'),f.get('title'),f.get('scope'))
 def walk(x):
  if isinstance(x,dict):
   if x.get('mathdb_id') in ids:print('MATCH',x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(d)
