import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r711';R=L/'pi-mathdb-full-corpus-inventory-r301'
ids=set(json.loads((I/'reserved-ids-r712.json').read_text())['ids']);out=[]
for c in sorted((R/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,line in enumerate(c.open(),1):
  d=json.loads(line)
  if d.get('mathdb_id',d.get('id')) in ids:
   out.append({'chunk':str(c),'line':n,'record':d,'canonical_record_sha256':hashlib.sha256(json.dumps(d,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('keys',list(out[0]['record']))
for d in out:
 r=d['record'];print(json.dumps(r,ensure_ascii=False))
