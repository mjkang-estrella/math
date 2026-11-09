exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("bind={}")[0])
ids=set(j(I/'reserved-ids-r708.json')['ids']); rows=[]
for p in sorted((R/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if int(r.get('id',r.get('mathdb_id',-1))) in ids:
   rows.append({'record':r,'chunk':str(p),'line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(O/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('record keys',list(rows[0]['record']))
for x in rows:
 r=x['record']; print('\nID',r.get('id',r.get('mathdb_id')),json.dumps(r,ensure_ascii=False))
