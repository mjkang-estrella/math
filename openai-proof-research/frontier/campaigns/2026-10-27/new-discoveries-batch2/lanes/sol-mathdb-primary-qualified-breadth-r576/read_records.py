exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('refs=')[0])
ids=set(load(I/'reserved-ids.json')['ids']);q=load(I/'queue.json');assert {x['mathdb_id'] for x in q}==ids and len(q)==50
cov=set(map(int,load(I/'coverage-delta.json')));assert len(cov)==5333
sets=[set(x['ids']) for x in load(I/'active-breadth-reservations.json')];assert len(sets)==3
for j,s in enumerate(sets):
 assert len(s)==50 and not s&cov and not s&set(load(I/'reserved-ids.json')['protected_ids'])
 for t in sets[:j]:assert not s&t
assert ids in sets
rows=[]
for p in sorted((R/'corpus').glob('*.jsonl')):
 for ln,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:rows.append(dict(mathdb_id=r['mathdb_id'],chunk=str(p),line=ln,statement=r['statement'],statement_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),record=r))
assert len(rows)==50 and {x['mathdb_id'] for x in rows}==ids
(D/'literal-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(D/'reconciliation.json').write_text(json.dumps(dict(baseline_records=5333,assignment=50,all_active_sets=[len(s) for s in sets],disjoint=True,protected_excluded=True),indent=2)+'\n')
for r in rows:print('\nID',r['mathdb_id'],r['record']['title'],'\n',r['statement'],'\nSOURCE',r['record']['source_url'])
