exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("(O/'initial-bindings.json')")[0])
q=load(I/'queue-r688.json');res=load(I/'reserved-ids-r688.json');ids=set(res['ids']);cov=load(I/'coverage-delta.json');assert len(cov)==8083
sets=[set(r['ids']) for r in load(I/'active-breadth-reservations.json')]
assert ids=={r['mathdb_id'] for r in q} and len(ids)==50
for i,s in enumerate(sets):
 assert not s&set(map(int,cov)) and not s&set(res['protected_ids'])
 for t in sets[i+1:]:assert not s&t
rows=[]
for e in chunks:
 p=R/e['path']
 for line,b in enumerate(p.open('rb'),1):
  r=json.loads(b)
  if r.get('mathdb_id',r.get('id')) in ids:
   rows.append({'corpus_path':str(p),'line':line,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
(O/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('reservation and disjointness PASS; first record keys:',list(rows[0]['record']))
for r in rows: print(json.dumps(r,ensure_ascii=False))
