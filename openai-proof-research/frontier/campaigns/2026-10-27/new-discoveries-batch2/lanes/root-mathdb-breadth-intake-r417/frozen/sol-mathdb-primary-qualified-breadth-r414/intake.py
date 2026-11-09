from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;L=R.parent;I=L/'root-mathdb-breadth-intake-r413'
r=json.loads((I/'reserved-ids.json').read_text());ids=set(r['ids']);old=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==50 and len(old)==1733
assert not ids&set(map(int,old)) and not ids&set(r['other_active_reservations']) and not ids&{372627,372628,368940}
b=json.loads((R/'bindings.json').read_text());found={}
for e in b['chunks']:
 for line in Path(e['absolute']).open():
  x=json.loads(line)
  if x['mathdb_id'] in ids:
   assert x['mathdb_id'] not in found
   found[x['mathdb_id']]=x
assert set(found)==ids
rows=[]
for n in r['ids']:
 x=found[n];rows.append({'record':x,'statement_sha256':hashlib.sha256(x['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
(R/'selected-records.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(R/'assignment-check.json').write_text(json.dumps({'assigned':r['ids'],'reviewed_count':len(old),'other_reserved_count':len(r['other_active_reservations']),'exactset':True,'disjoint':True},indent=2)+'\n')
for row in rows:
 x=row['record'];print('\nID',x['mathdb_id'],x['title'],'\nSOURCE',x['source_url'],'\n'+x['statement'])
