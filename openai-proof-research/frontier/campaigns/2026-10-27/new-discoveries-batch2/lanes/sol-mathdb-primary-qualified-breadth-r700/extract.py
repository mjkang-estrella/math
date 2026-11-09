exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("bindings=[")[0])
r=json.loads((I/'reserved-ids-r700.json').read_text()); cov=json.loads((I/'coverage-delta.json').read_text()); assert len(cov)==8383
sets=json.loads((I/'active-breadth-reservations.json').read_text()); allids=set(); checks=[]
for s in sets:
 ids=set(s['ids']); assert len(ids)==50 and not ids&set(map(int,cov)) and not ids&allids and not ids&set(s['protected_ids']);allids|=ids;checks.append({'lane':s['lane'],'ids':s['ids'],'disjoint':True})
assert set(r['ids'])=={e['mathdb_id'] for e in json.loads((I/'queue-r700.json').read_text())}
(D/'reservation-checks.json').write_text(json.dumps({'baseline':len(cov),'sets':checks},indent=2)+'\n')
rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  rec=json.loads(line)
  if int(rec.get('id',rec.get('mathdb_id',-1))) in r['ids']:
   rows.append({'chunk':str(p),'line':n,'record':rec,'canonical_record_sha256':hashlib.sha256(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print('PASS reservation disjointness; 50 literals extracted; record keys:',rows[0]['record'].keys())
for x in rows: print(json.dumps(x,ensure_ascii=False))
