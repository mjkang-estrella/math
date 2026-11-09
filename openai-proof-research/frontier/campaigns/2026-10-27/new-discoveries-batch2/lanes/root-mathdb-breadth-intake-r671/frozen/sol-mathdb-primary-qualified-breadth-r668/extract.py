exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("print('inventory keys'")[0])
refs=load(O/'initial-bindings.json')
for d,names in [('root-mathdb-accepted-exclusions-r304',['accepted-exclusions.json','historical-dispositions.json']),('root-mathdb-cayley-review-intake-r363',['DECISION.md','disposition.json'])]:
 for n in names:refs.append(bind(L/d/n))
(O/'initial-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
c=load(I/'coverage-delta.json');print('coverage keys',c.keys())
for k,v in c.items():print(k, str(v)[:500])
q=load(I/'queue-r668.json');res=load(I/'reserved-ids-r668.json');ids=set(res['ids']);assert len(ids)==50 and ids=={x['mathdb_id'] for x in q}
active=load(I/'active-breadth-reservations.json');sets=[set(x['ids']) for x in active]
for j,s in enumerate(sets):
 assert not s&set(res['protected_ids'])
 for t in sets[j+1:]:assert not s&t
records=[]
for e in chunks:
 p=R/e['path']
 for line,b in enumerate(p.open('rb'),1):
  r=json.loads(b)
  if r.get('id',r.get('mathdb_id')) in ids:
   records.append(dict(mathdb_id=r.get('id',r.get('mathdb_id')),chunk=str(p),line=line,literal_line_sha256=hashlib.sha256(b).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),record=r))
assert len(records)==50
(O/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
for x in records:
 r=x['record'];print('\nID',x['mathdb_id'],'KEYS',list(r) if len(records)==0 else '');print(json.dumps(r,ensure_ascii=False))
