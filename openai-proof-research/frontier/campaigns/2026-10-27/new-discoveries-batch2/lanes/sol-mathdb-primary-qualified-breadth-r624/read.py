exec(open(__file__.replace('read.py','bind.py')).read().split("q=j(I/")[0].split("refs={}")[0])
ids=set(j(I/'reserved-ids-r624.json')['ids']); out=[]
for p in sorted((R/'corpus').glob('*.jsonl')):
 for ln,b in enumerate(p.open('rb'),1):
  x=json.loads(b)
  if x.get('id',x.get('mathdb_id')) in ids:
   out.append({'record':x,'chunk':str(p),'line':ln,'literal_line_sha256':hashlib.sha256(b).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(D/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:print(json.dumps(x['record'],ensure_ascii=False))
