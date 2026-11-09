exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("for name in ['queue.json'")[0])
ids=set(json.loads((I/'reserved-ids.json').read_bytes())['ids']);cov=json.loads((I/'coverage-delta.json').read_bytes());assert len(cov)==4683
sets=[set(x['ids']) for x in json.loads((I/'active-breadth-reservations.json').read_bytes())]; assert ids in sets
for i,s in enumerate(sets):
 assert not s&set(map(int,cov));assert not s&set(json.loads((I/'reserved-ids.json').read_bytes())['protected_ids'])
 for t in sets[:i]:assert not s&t
records=[]
for e in chunks:
 for n,line in enumerate((p.parent/e['path']).open(),1):
  v=json.loads(line)
  if v.get('id',v.get('mathdb_id')) in ids:
   records.append(dict(chunk=e['path'],line=n,record=v))
assert len(records)==50
(D/'assigned-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('SCHEMA',list(records[0]['record']))
for x in records:
 v=x['record'];print('\nID',v.get('id',v.get('mathdb_id')),'\n',json.dumps(v,ensure_ascii=False))
