exec((__import__('pathlib').Path(__file__).parent/'prepare.py').read_text())
selected={}
for x in chunks:
 p=R/x['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if int(r.get('id',r.get('mathdb_id',-1))) in ids:
   i=int(r.get('id',r.get('mathdb_id')));selected[i]=dict(mathdb_id=i,corpus_path=str(p),line=n,literal_line_sha256=hashlib.sha256(line.encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),record=r)
assert set(selected)==set(ids)
(D/'literal-records.json').write_text(json.dumps([selected[i] for i in ids],ensure_ascii=False,indent=2)+'\n')
for i in ids:print(json.dumps(selected[i],ensure_ascii=False))
