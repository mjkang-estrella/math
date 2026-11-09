exec(open(__file__.replace('read.py','freeze.py')).read().split("print('r304 dirs'")[0])
r=load(I/'reserved-ids.json');q=load(I/'queue.json');cov=load(I/'coverage-delta.json');ids=set(r['ids']);assert len(ids)==50 and ids=={x['mathdb_id'] for x in q};assert len(cov)==1783;assert not ids.intersection(map(int,cov));assert not ids.intersection(r['other_active_reservations']);assert not ids.intersection([372627,372628,368940])
(L/'assignment-check.json').write_text(json.dumps({'assignment':sorted(ids),'reviewed_count':len(cov),'disjoint_reviewed':True,'disjoint_active':True,'disjoint_special':True},indent=2)+'\n')
# Inspect only selected rows; no other active statement is emitted or retained.
records=[]
for p in sorted((C/'corpus').glob('*chunk*.jsonl')):
 for n,line in enumerate(p.open(),1):
  x=json.loads(line)
  if x.get('mathdb_id',x.get('id')) in ids:
   records.append({'original':str(p),'line':n,'record':x})
print('selected',len(records))
(L/'records.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(records[0],ensure_ascii=False,indent=2))
