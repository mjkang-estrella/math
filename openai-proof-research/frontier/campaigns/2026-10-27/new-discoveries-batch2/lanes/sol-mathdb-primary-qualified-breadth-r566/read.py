exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("bind(I/'manifest.json'")[0])
ids=set(j(I/'reserved-ids.json')['ids']);q=j(I/'queue.json');assert ids=={r['mathdb_id'] for r in q} and len(ids)==50
cov=j(I/'coverage-delta.json');assert len(cov)==5083
seen=set()
for r in j(I/'active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
rows=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'record':r})
assert len(rows)==50
rows.sort(key=lambda r:r['mathdb_id']);(P/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for i,r in enumerate(rows):
 print('\nINDEX',i,'ID',r['mathdb_id'],'\n'+r['statement'])
print('\nCONTEXT\n', (I/'adjudications.json').read_text(),(I/'hypothesis-queue.json').read_text())
