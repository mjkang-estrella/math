import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent; B=L.parent;I=B/'pi-mathdb-full-corpus-inventory-r301';T=B/'root-mathdb-breadth-intake-r449'
r=json.loads((T/'reserved-ids.json').read_text());print('RESERVATIONS',json.dumps(r)); ids=set(r['ids']);cov=json.loads((T/'coverage-delta.json').read_text());assert len(cov)==2633;assert not ids&set(map(int,cov));assert not ids&{372627,372628,368940,404067,364119}
out=[]
for p in sorted((I/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  a=json.loads(line)
  if a.get('mathdb_id',a.get('id')) in ids:out.append({'record':a,'original_chunk':str(p),'original_line':n,'canonical_record_hash':hashlib.sha256(json.dumps(a,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()})
assert len(out)==50
(L/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
