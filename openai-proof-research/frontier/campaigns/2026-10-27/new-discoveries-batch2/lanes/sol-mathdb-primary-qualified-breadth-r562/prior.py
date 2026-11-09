import pathlib,json
P=pathlib.Path(__file__).parent;L=P.parent;ids={d['mathdb_id'] for d in json.loads((P/'dispositions.json').read_text())};output=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;obj=json.loads(p.read_text())
 def walk(o):
  if isinstance(o,dict):
   hits=[i for i in ids if str(i) in json.dumps(o)]
   if hits and ('mathdb_id' in o or 'mathdb_ids' in o or 'record_associations' in o):output.append({'file':str(p),'hits':hits,'entry':o})
   for v in o.values():walk(v)
  elif isinstance(o,list):
   for v in o:walk(v)
 walk(obj)
 if name=='accepted-exclusions.json':
  for f in obj['families']:print(f['number'],f['title'],f.get('scope',''))
print('DIRECT ID CONTEXT MATCHES',json.dumps(output,ensure_ascii=False))
(P/'prior-context-matches.json').write_text(json.dumps(output,ensure_ascii=False,indent=2)+'\n')
