from bind import D,L,I,C,load
import json,hashlib
q=load(I/'queue-r626.json'); ids={x['mathdb_id'] for x in q}
print('RESERVATION',load(I/'reserved-ids-r626.json'))
cov=load(I/'coverage-delta.json'); assert len(cov)==6583
sets=load(I/'active-breadth-reservations.json')
for a in sets:
 s=set(a['ids']); assert not s & set(map(int,cov)); assert not s & set(a['protected_ids']); assert not s&set(a['other_active_reservations'])
assert len(ids)==50 and ids==set(next(a['ids'] for a in sets if a['lane']==D.name))
rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'record':r,'corpus_path':str(p),'line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest()})
assert len(rows)==50
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for x in rows:
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'],r['references'])
print('\nCONTEXT')
for p in [I/'adjudications.json',I/'focused-assignment.json',I/'hypothesis-queue.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(p.name,p.read_text())
print('LEDGER',load(L.parent/'ledger.json').keys())
print('PRIOR',str(load(L.parent/'prior-campaign-context.json'))[:3000])
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 v=load(C/'frozen/root-mathdb-accepted-exclusions-r304'/name)
 print(name,str(v)[:1800])
