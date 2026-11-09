exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text())
ids=set(j(I/'reserved-ids.json')['ids']);assert len(ids)==50
cov=j(I/'coverage-delta.json');assert len(cov)==4983
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert ids=={r['mathdb_id'] for r in j(I/'queue.json')}
rows=[]
for e in chunks:
 p=C/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
(P/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for d in rows:print('\nID',d['mathdb_id'],json.dumps(d['record'].get('sources',d['record'].get('source',{})),ensure_ascii=False),'\n',d['statement'])
