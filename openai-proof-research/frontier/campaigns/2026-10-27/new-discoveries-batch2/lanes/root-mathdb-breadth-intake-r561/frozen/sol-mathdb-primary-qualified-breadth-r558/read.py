exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("m=json.loads")[0])
refs=json.loads((D/'flat-bindings.json').read_text())
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:
 p=L/rel;refs.append(h(p))
save('flat-bindings.json',refs)
q=json.loads((I/'queue.json').read_text());res=json.loads((I/'reserved-ids.json').read_text());cov=json.loads((I/'coverage-delta.json').read_text());sets=json.loads((I/'active-breadth-reservations.json').read_text())
assert len(cov)==4883
seen=set()
for r in sets:
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(res['protected_ids']);seen|=s
assert set(x['mathdb_id'] for x in q)==set(res['ids'])
records=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  x=json.loads(line)
  if x.get('id',x.get('mathdb_id')) in res['ids']:
   records.append({'chunk':str(p),'line':n,'record':x,'canonical_record_sha256':hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
save('assigned-records.json',records)
print('records',len(records));print('first keys',records[0]['record'].keys())
for r in records:
 x=r['record'];print('\nID',x.get('id',x.get('mathdb_id')),x.get('title'));print(x.get('statement',x.get('problem_statement',x.get('content'))));print('source',x.get('sources',x.get('source')))
