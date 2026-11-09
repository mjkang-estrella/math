from bind import D,L,I,load,bind,rows
import json,hashlib
for p in (L/'root-mathdb-cayley-review-intake-r363').glob('*'):
 if p.is_file():bind(p)
(D/'flat-bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
ids=set(load(I/'reserved-ids-r630.json')['ids']);found=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r.get('mathdb_id',r.get('id')) in ids:
   found.append({'chunk':str(p),'line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(found)==50
(D/'literal-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
for x in found:print(json.dumps(x,ensure_ascii=False))
