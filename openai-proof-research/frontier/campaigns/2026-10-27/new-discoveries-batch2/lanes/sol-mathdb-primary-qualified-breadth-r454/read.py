exec('import pathlib,json,hashlib')
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r453';V=B/'pi-mathdb-full-corpus-inventory-r301'
ids=json.loads((I/'reserved-ids.json').read_text())['ids'];out=[]
for p in sorted((V/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('id',r.get('mathdb_id')) in ids:
   out.append(dict(record=r,original_chunk=str(p),original_line=n,canonical_record_sha256=hashlib.sha256(json.dumps(r,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()))
assert len(out)==50
(L/'assigned-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('keys',list(out[0]['record']))
for x in out:
 r=x['record']; print('\nID',r.get('id',r.get('mathdb_id'))); print(json.dumps(r,ensure_ascii=False))
