exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('for n in [585,587]:')[0])
I=L/'root-mathdb-breadth-intake-r585';ids=set(load(I/'reserved-ids.json')['ids']);out=[]
for p in sorted((R/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if int(r.get('id',r.get('mathdb_id',0))) in ids:
   out.append({'id':int(r.get('id',r.get('mathdb_id'))),'chunk':str(p),'line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50;dump('literal-records.json',out)
print('record keys',out[0]['record'].keys())
for x in out:print(x['id'],json.dumps(x['record'],ensure_ascii=False))
