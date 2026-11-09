exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("(D/'flat-bindings.json')")[0])
q=json.loads((I/'queue-r606.json').read_text());ids={x['mathdb_id'] for x in q};rows=[]
for x in chunks:
 p=R/x['path']
 for n,s in enumerate(p.open(),1):
  r=json.loads(s)
  if r.get('id',r.get('mathdb_id')) in ids:
   rows.append({'chunk':str(p),'line':n,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for r in rows:print(json.dumps(r,ensure_ascii=False))
