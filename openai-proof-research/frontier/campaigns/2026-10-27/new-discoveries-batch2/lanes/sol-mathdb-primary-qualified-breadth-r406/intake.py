exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('for n in [')[0])
f=json.loads((L/'frozen-references.json').read_text());res=json.loads((I/'reserved-ids.json').read_text());ids=set(res['ids']);cov=json.loads((I/'coverage-delta.json').read_text());assert len(ids)==50 and len(cov)==1533;assert not ids&set(map(int,cov));assert not ids&set(res['other_active_reservations']);assert not ids&{372627,372628,368940}
queue=json.loads((I/'queue.json').read_text());assert ids=={r['mathdb_id'] for r in queue}
records=[]
for cp in f['corpus_chunks']:
 for line in Path(cp).open():
  r=json.loads(line)
  if int(r.get('id',r.get('mathdb_id',-1))) in ids:records.append({'chunk':cp,'record':r})
assert len(records)==50,len(records)
(L/'selected-records.json').write_text(json.dumps(records,indent=2)+'\n')
(L/'assignment-receipt.json').write_text(json.dumps({'assigned':sorted(ids),'assigned_count':50,'reviewed_count':len(cov),'disjoint_reviewed':True,'disjoint_active':True,'disjoint_special':True,'queue_exactset':True},indent=2)+'\n')
print(json.dumps(records[0],indent=2))
