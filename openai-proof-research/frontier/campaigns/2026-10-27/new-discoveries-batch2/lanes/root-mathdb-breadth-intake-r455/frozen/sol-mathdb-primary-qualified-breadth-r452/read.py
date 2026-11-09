exec(compile(open(__file__.replace('read.py','preflight.py')).read(),__file__.replace('read.py','preflight.py'),'exec'))
q=json.loads((B/'root-mathdb-breadth-intake-r451/reserved-ids.json').read_text()); ids=set(q['ids']); assert len(ids)==50 and not ids.intersection(q['other_active_reservations'])
cov=json.loads((B/'root-mathdb-breadth-intake-r451/coverage-delta.json').read_text()); assert len(cov)==2683; assert not ids.intersection(map(int,cov)); assert not ids.intersection([372627,372628,368940,404067,364119])
rows=[]
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for i,line in enumerate(p.open(),1):
  r=json.loads(line); key=r.get('id',r.get('mathdb_id'))
  if key in ids: rows.append({'record':r,'original_chunk':str(p),'original_line':i,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(L/'records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('schema',rows[0]['record'].keys()); print(json.dumps(rows[0],ensure_ascii=False,indent=2))
