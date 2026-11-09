exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('for n in [')[0])
ids=set(j(I/'reserved-ids.json')['ids']);cov=j(I/'coverage-delta.json');assert len(cov)==5783
sets=[set(r['ids']) for r in j(I/'active-breadth-reservations.json')]
for a in sets:
 assert len(a)==50 and not a&set(map(int,cov)) and not a&set(j(I/'reserved-ids.json')['protected_ids'])
 for b in sets:
  if a is not b:assert not a&b
rows=[]
for f in sorted((C/'corpus').glob('*.jsonl')):
 for n,s in enumerate(f.open(),1):
  r=json.loads(s)
  if r['mathdb_id'] in ids:
   rows.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(f),'corpus_line':n,'statement':r['statement'],'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'record':r})
assert len(rows)==50
(P/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
for d in rows:print('\nID',d['mathdb_id'],json.dumps(d['record'],ensure_ascii=False))
