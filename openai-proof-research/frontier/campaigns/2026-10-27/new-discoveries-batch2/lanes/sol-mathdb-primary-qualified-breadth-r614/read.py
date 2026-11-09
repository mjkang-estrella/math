exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("(L/'flat-bindings.json')")[0])
q=load(I/'queue-r614.json'); ids={x['mathdb_id'] for x in q}; cov=load(I/'coverage-delta.json');assert len(cov)==6283
rs=load(I/'active-breadth-reservations.json'); seen=set()
for r in rs:
 s=set(r['ids']);assert not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert ids==set(load(I/'reserved-ids-r614.json')['ids'])
rows=[]
for x in chunks:
 p=R/x['path']
 for n,line in enumerate(p.open(),1):
  d=json.loads(line)
  if int(d.get('mathdb_id',d.get('id',0))) in ids:
   rows.append({'chunk':str(p),'line':n,'record':d,'canonical_record_sha256':hashlib.sha256(json.dumps(d,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(L/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('DISJOINT PASS; records',len(rows));print('record keys',rows[0]['record'].keys())
for x in rows:
 d=x['record'];print('\nID',d.get('mathdb_id',d.get('id')),json.dumps(d,ensure_ascii=False))
print('ADJ',load(I/'adjudications.json'));print('HYP',load(I/'hypothesis-queue.json'))
