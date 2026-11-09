import json,pathlib
P=pathlib.Path(__file__).parent;L=P.parent
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;d=json.loads(p.read_text())
 if name.startswith('accepted'):
  for f in d['families']: print(f.get('number'),f.get('title'),f.get('scope'))
 else:
  ids=[str(x['record']['mathdb_id']) for x in json.loads((P/'literal-records.json').read_text())]
  print('historical direct IDs',[x for x in ids if x in json.dumps(d)])
