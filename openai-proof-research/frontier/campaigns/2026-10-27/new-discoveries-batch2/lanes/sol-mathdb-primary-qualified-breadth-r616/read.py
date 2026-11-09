exec(open(__file__.replace('read.py','bind.py')).read().split("print('BOUND'")[0])
q=j(I/'queue-r616.json');ids={x['mathdb_id'] for x in q};r=j(I/'reserved-ids-r616.json');cov=j(I/'coverage-delta.json');assert len(cov)==6333 and ids==set(r['ids']) and not ids&{int(x) for x in cov}
a=j(I/'active-breadth-reservations.json');seen=set()
for x in a:
 s=set(x['ids']);assert not s&seen and not s&{int(k) for k in cov} and not s&set(x['protected_ids']);seen|=s
records=[]
for f in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(f.open(),1):
  x=json.loads(line)
  if x['mathdb_id'] in ids:
   records.append({'record':x,'chunk':str(f),'line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'statement_utf8_sha256':hashlib.sha256(x['statement'].encode()).hexdigest()})
assert len(records)==50
(P/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
for x in records:
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'\n',r['statement'],'\nSOURCE',r['source_url'])
print('CONTEXT')
for f in [I/'adjudications.json',I/'hypothesis-queue.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(f.name,f.read_text()[:9000])
