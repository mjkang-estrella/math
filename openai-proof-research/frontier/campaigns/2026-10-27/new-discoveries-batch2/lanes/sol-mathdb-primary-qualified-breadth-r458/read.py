exec(compile(open(__file__.replace('read.py','freeze.py')).read().split("rows=sorted")[0], 'local-freeze-definitions','exec'))
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for r in json.loads((B/name/'bindings.json').read_text()):
  for key in ['original','copy']:
   if key in r:bind(Path(r[key]) if Path(r[key]).is_absolute() else B/name/r[key],r)
rows=sorted(refs.values(),key=lambda r:r['path']); (L/'frozen_inputs.json').write_text(json.dumps(rows,indent=2)+'\n');(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'freeze-receipt-final.json').write_text(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'flat_files':len(rows),'sha256':H((L/'frozen_inputs.json').read_bytes())},indent=2)+'\n')
r=json.loads((I/'reserved-ids.json').read_text());ids=set(r['ids']);q=json.loads((I/'queue.json').read_text());cov=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==50 and ids=={x['mathdb_id'] for x in q}
assert not ids.intersection(r['other_active_reservations']) and not ids.intersection(map(int,cov))
assert not ids.intersection([372627,372628,368940,404067,364119])
def idwalk(j):
 out=set()
 if isinstance(j,dict):
  for k,v in j.items():
   if k in ['mathdb_id','mathdb_ids','problem_ids']:out.update([v] if isinstance(v,int) else v if isinstance(v,list) else [])
   else:out.update(idwalk(v))
 elif isinstance(j,list):
  for v in j:out.update(idwalk(v))
 return out
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 assert not ids.intersection(idwalk(json.loads((B/'root-mathdb-accepted-exclusions-r304'/f).read_text())))
found=[]
for ch in chunks:
 p=B/'pi-mathdb-full-corpus-inventory-r301'/ch['path']
 for no,line in enumerate(p.open(),1):
  x=json.loads(line)
  if x.get('mathdb_id',x.get('id')) in ids:
   found.append({'original_chunk':str(p),'original_line':no,'raw_line_sha256':H(line.encode()),'canonical_record_sha256':H(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'record':x})
assert len(found)==50
(L/'assigned-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
print('DISJOINT PASS; prior coverage',len(cov),'records',len(found));print('SCHEMA',found[0]['record'].keys())
for v in found:
 print(json.dumps(v['record'],ensure_ascii=False))
