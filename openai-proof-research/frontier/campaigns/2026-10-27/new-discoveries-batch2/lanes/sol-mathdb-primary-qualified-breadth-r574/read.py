exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('out={}')[0])
r=j(I/'reserved-ids.json');ids=set(r['ids']);cov=j(I/'coverage-delta.json');assert len(cov)==5283
sets=[set(x['ids']) for x in j(I/'active-breadth-reservations.json') if x['lane']!=r['lane']]+[ids]
for i,a in enumerate(sets):
 assert len(a)==50 and not a&set(map(int,cov)) and not a&set(r['protected_ids'])
 for b in sets[:i]:assert not a&b
assert set().union(*sets[:-1])==set(r['other_active_reservations'])
assert {x['mathdb_id'] for x in j(I/'queue.json')}==ids
rows=[]
for ch in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(ch.open(),1):
  v=json.loads(line)
  if v['mathdb_id'] in ids:
   rows.append({'record':v,'chunk':str(ch),'line':n,'statement_utf8_sha256':hashlib.sha256(v['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(v,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(P/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(P/'reservation-check.json').write_text(json.dumps({'baseline':5283,'assignment':50,'other_reservations':[len(s) for s in sets[:-1]],'pairwise_disjoint':True,'protected_disjoint':True},indent=2)+'\n')
for x in rows:
 v=x['record'];print('\n###',v['mathdb_id'],v['title'],'\n'+v['statement']+'\nSOURCE '+str(v['source_url']))
