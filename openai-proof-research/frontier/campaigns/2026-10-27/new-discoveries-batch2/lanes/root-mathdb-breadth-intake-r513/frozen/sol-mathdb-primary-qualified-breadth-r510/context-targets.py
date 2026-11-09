import pathlib,json
P=pathlib.Path(__file__).resolve().parent;L=P.parent;ids={x['mathdb_id'] for x in json.loads((P/'assigned-records.json').read_text())}
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 a=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text())
 print(n,'schema',list(a) if isinstance(a,dict) else len(a))
 def walk(x):
  if isinstance(x,dict):
   if x.get('mathdb_id') in ids:print(json.dumps(x,ensure_ascii=False))
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(a)
 if n.startswith('accepted'):print('ALL ACCEPTED FAMILY TITLES:',*[f['title'] for f in a['families']],sep='\n')
for n in ['ledger.json','prior-campaign-context.json']:
 a=json.loads((L.parent/n).read_text());print(n,'top-level:',list(a) if isinstance(a,dict) else len(a))
