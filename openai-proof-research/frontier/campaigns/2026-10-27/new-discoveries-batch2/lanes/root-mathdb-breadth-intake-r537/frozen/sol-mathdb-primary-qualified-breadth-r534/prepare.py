exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text())
# Bind Cayley decision at corrected actual lane before reading.
p=L/'root-mathdb-cayley-review-intake-r363';out=json.loads((D/'flat-bindings.json').read_text())
for f in p.iterdir():
 if f.is_file():out.append(info(f))
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
r=json.loads((I/'reserved-ids.json').read_text());q=json.loads((I/'queue.json').read_text());ids=r['ids'];assert len(ids)==50 and [x['mathdb_id'] for x in q]==ids
cov=json.loads((I/'coverage-delta.json').read_text());assert len(cov)==4283
sets=[set(x['ids']) for x in json.loads((I/'active-breadth-reservations.json').read_text())];print('reserved sizes',list(map(len,sets)))
for j,s in enumerate(sets):
 assert not s&set(map(int,cov));assert not s&set(r['protected_ids'])
 for t in sets[:j]:assert not s&t
assert set(ids) in sets
rows=[]
for p in sorted((R/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  a=json.loads(line)
  if a['mathdb_id'] in ids:
   rows.append(dict(record=a,corpus_chunk=str(p),line=n,statement_sha256=hashlib.sha256(a['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(a,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()))
rows.sort(key=lambda x:ids.index(x['record']['mathdb_id']));assert len(rows)==50
(D/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(D/'statement-readout.txt').write_text('\n\n'.join(str(i+1)+' | '+str(a['record']['mathdb_id'])+' | '+a['record']['title']+'\n'+a['record']['statement']+'\nSOURCE '+str(a['record']['source_url']) for i,a in enumerate(rows)))
print('prepared 50')
