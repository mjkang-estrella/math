exec(open(__file__.replace('read.py','bind.py')).read().split("# Only structure")[0])
refs=read(D/'flat-bindings.json') # rebind all required references before record content
C=L/'pi-mathdb-full-corpus-inventory-r301';cm=read(C/'manifest.json')
for x in [x for x in cm['files'] if x['path'].startswith('corpus/')]+cm['frozen_inputs']:
 a=digest(C/x['path']);assert a['sha256']==x['sha256'] and a['size']==x['bytes'];refs.append(a)
for p in [L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 refs.append(digest(p))
(D/'flat-bindings.json').write_text(json.dumps(list({x['path']:x for x in refs}.values()),indent=2)+'\n')
cov=read(I/'coverage-delta.json');assert len(cov)==6183
active=read(I/'active-breadth-reservations.json');seen=set()
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
ids=set(read(I/'reserved-ids-r610.json')['ids']);assert ids=={r['mathdb_id'] for r in read(I/'queue-r610.json')}
rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append({'corpus_chunk':str(p),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('DISJOINTNESS PASS; literal 50/50')
for x in rows:
 r=x['record'];print('\nID',r['mathdb_id'],r.get('title'));print(r['statement']);print('SOURCE',r.get('sources',r.get('source')))
print('record keys',list(rows[0]['record']))
