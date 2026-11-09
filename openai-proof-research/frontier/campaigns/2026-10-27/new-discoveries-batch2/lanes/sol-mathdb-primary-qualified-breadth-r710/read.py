exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('out=[]')[0])
ids=set(j(I/'reserved-ids-r710.json')['ids']); found=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line);rid=r.get('mathdb_id',r.get('id'))
  if rid in ids:
   found.append({'mathdb_id':rid,'corpus_chunk':str(p),'corpus_line':n,'record':r,'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(found)==50
(P/'literal-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
for f in found:
 print(json.dumps(f,ensure_ascii=False))
