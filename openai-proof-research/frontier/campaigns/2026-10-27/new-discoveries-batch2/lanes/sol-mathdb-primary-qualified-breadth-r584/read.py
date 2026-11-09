exec(open(__file__.replace('read.py','bind.py')).read().split("print('BOUND'")[0])
c=load(I/'coverage-delta.json');a=load(I/'active-breadth-reservations.json');print('COVERAGE',str(c)[:1800]);print('ACTIVE',str(a)[:1500])
ids=set(load(I/'reserved-ids.json')['ids']);out=[]
for x in chunks:
 p=R/x['path']
 for lineno,line in enumerate(p.open(),1):
  row=json.loads(line)
  if int(row.get('mathdb_id',row.get('id',0))) in ids:
   out.append({'id':row.get('mathdb_id',row.get('id')),'chunk':str(p),'line':lineno,'record':row,'canonical_record_sha256':hashlib.sha256(json.dumps(row,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
dump('literal-records.json',out)
print('FIRST RECORD',out[0])
for p in [I/'adjudications.json',I/'hypothesis-queue.json',L/'sol-mathdb-primary-qualified-breadth-r578/failures.json',L/'sol-mathdb-primary-qualified-breadth-r542/failures.md',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print('\nCONTEXT',p,p.read_text())
for p in [L/'root-mathdb-accepted-exclusions-r304'/n for n in ['accepted-exclusions.json','historical-dispositions.json']]+[L.parent/'ledger.json',L.parent/'prior-campaign-context.json']:
 v=load(p);print('PRIOR',p, str(v)[:1400]);print('ASSIGNED_ID_OCCURRENCES',[i for i in ids if str(i) in p.read_text()])
