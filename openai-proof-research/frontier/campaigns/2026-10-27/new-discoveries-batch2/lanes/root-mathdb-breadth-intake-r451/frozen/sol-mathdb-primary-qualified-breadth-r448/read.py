exec((__import__('pathlib').Path(__file__).parent/'preflight.py').read_text().split('for lane in')[0])
A=L/'root-mathdb-breadth-intake-r447';ids=load(A/'reserved-ids.json')['ids']; assert len(ids)==len(set(ids))==50
assert not set(map(str,ids))&set(load(A/'coverage-delta.json'))
print('reservation keys',list(load(A/'reserved-ids.json')))
print('r304 keys',list(load(L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json')))
print('r363 disposition',load(L/'root-mathdb-cayley-review-intake-r363/disposition.json'))
assert not set(ids)&{372627,372628,368940,404067,364119}
records=[];loc=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 with p.open() as f:
  for i,line in enumerate(f,1):
   r=json.loads(line)
   if int(r.get('mathdb_id',r.get('id',-1))) in ids:records.append(r);loc.append({'id':r.get('mathdb_id',r.get('id')),'path':str(p),'line':i})
assert len(records)==50
(O/'records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n');(O/'record-locations.json').write_text(json.dumps(loc,indent=2)+'\n')
print('assigned record keys',list(records[0]))
for r in records:print(json.dumps(r,ensure_ascii=False))
