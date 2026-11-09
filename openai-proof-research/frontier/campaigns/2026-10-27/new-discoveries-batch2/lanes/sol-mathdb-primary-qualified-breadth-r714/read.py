exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text())
ids=set(reservations[-1]['ids']);out=[]
for e in chunks:
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r.get('id',r.get('mathdb_id')) in ids:
   out.append(dict(id=r.get('id',r.get('mathdb_id')),chunk=e['path'],line=n,record=r,canonical_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),literal_line_sha256=hashlib.sha256(line.encode()).hexdigest()))
assert len(out)==50
out.sort(key=lambda x:x['id']);(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:print(json.dumps(x,ensure_ascii=False))
