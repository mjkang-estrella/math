exec(open(__file__.replace('extract.py','freeze.py')).read().split('for n in names:')[0])
refs=json.loads((L/'bindings.json').read_text())
for n in ['root-mathdb-breadth-intake-r461','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 for e in json.loads((B/n/'bindings.json').read_text()):
  p=pathlib.Path(e['original']);assert h(p)==e['sha256'],str(p)
  if 'size' in e:assert p.stat().st_size==e['size']
  bind(p,'direct-binding-original-no-expansion')
(L/'bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
r=json.loads((B/names[0]/'reserved-ids.json').read_text());q=json.loads((B/names[0]/'queue.json').read_text());ids=r['ids'];cov=json.loads((B/names[0]/'coverage-delta.json').read_text())
assert len(ids)==len(set(ids))==50;assert [x['mathdb_id'] for x in q]==ids
assert not set(ids)&set(r['other_active_reservations']);assert not set(map(str,ids))&set(cov);assert not set(ids)&{372627,372628,368940,404067,364119}
a=json.loads((B/names[2]/'accepted-exclusions.json').read_text()); hist=json.loads((B/names[2]/'historical-dispositions.json').read_text())
print('coverage',len(cov),'lookup keys',list(a['mathdb_lookup'])[:10]);print('history',[(k,type(v).__name__) for k,v in hist.items()])
# Exclude every numeric ID mentioned anywhere in exclusion/history payloads conservatively.
def ints(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if str(k).isdigit():yield int(k)
   yield from ints(v)
 elif isinstance(x,list):
  for v in x:yield from ints(v)
 elif isinstance(x,int):yield x
assert not set(ids)&set(ints(a));assert not set(ids)&set(ints(hist))
rows=[];chunks=sorted((B/names[1]/'corpus').glob('mathdb-normalized-chunk-*.jsonl'));assert len(chunks)==20
for p in chunks:
 for ln,s in enumerate(p.open(),1):
  x=json.loads(s)
  if x['mathdb_id'] in ids:
   rows.append(dict(record=x,original_chunk=str(p),original_line=ln,statement_sha256=hashlib.sha256(x['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()))
assert {x['record']['mathdb_id'] for x in rows}==set(ids) and len(rows)==50
rows.sort(key=lambda x:ids.index(x['record']['mathdb_id']))
(L/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(L/'assignment-receipt.json').write_text(json.dumps(dict(status='PASS',baseline_reported_statement_reviews=len(cov),records=50,chunks=20,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),bindings_sha256=h(L/'bindings.json')),indent=2)+'\n')
for x in rows:
 z=x['record'];print('\nID',z['mathdb_id'],z['title'],'\n',z['statement'],'\nSOURCES',json.dumps({k:v for k,v in z.items() if k not in ['statement','title','uuid']},ensure_ascii=False))
