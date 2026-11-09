import pathlib,json,hashlib,sys,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,e):
 b=p.read_bytes();assert H(b)==e['sha256'],str(p)
 assert len(b)==e.get('size',e.get('bytes',len(b))),str(p)
manifest=load(L/'manifest.json');excluded=set(manifest['excluded'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-excluded
assert actual=={e['path'] for e in manifest['files']},'exact payload membership'
for e in manifest['files']:check(L/e['path'],e)
for n in ['root-mathdb-breadth-intake-r461','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=B/n;m=load(d/'manifest.json');files=m if isinstance(m,list) else m['files']+m.get('frozen_inputs',[])
 for e in files:check(d/e['path'],e)
 if isinstance(m,dict) and 'frozen_inputs' in m:assert len(m['frozen_inputs'])==8
for e in load(L/'bindings.json'):check(pathlib.Path(e['path']),e)
assert H((L/'initial-bindings.json').read_bytes())==load(L/'freeze-receipt.json')['bindings_sha256']
r=load(B/'root-mathdb-breadth-intake-r461'/'reserved-ids.json');q=load(B/'root-mathdb-breadth-intake-r461'/'queue.json');ids=r['ids'];S=set(ids)
assert len(ids)==len(S)==50;assert [e['mathdb_id'] for e in q]==ids
assert not S&set(r['other_active_reservations']);assert not S&{372627,372628,368940,404067,364119}
cov=load(B/'root-mathdb-breadth-intake-r461'/'coverage-delta.json');assert len(cov)==2933 and not set(map(str,S))&set(cov)
def nums(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if str(k).isdigit():yield int(k)
   yield from nums(v)
 elif isinstance(x,list):
  for v in x:yield from nums(v)
 elif isinstance(x,int):yield x
for fn in ['accepted-exclusions.json','historical-dispositions.json']:assert not S&set(nums(load(B/'root-mathdb-accepted-exclusions-r304'/fn)))
chunks=sorted((B/'pi-mathdb-full-corpus-inventory-r301'/'corpus').glob('mathdb-normalized-chunk-*.jsonl'));assert len(chunks)==20
originals={}
for p in chunks:
 for ln,line in enumerate(p.open(),1):
  a=json.loads(line)
  if a['mathdb_id'] in S:
   assert a['mathdb_id'] not in originals;originals[a['mathdb_id']]=(a,str(p),ln)
records=load(L/'assigned-records.json');ds=load(L/'dispositions.json');assert len(records)==len(ds)==50
assert [d['mathdb_id'] for d in ds]==ids and [x['record']['mathdb_id'] for x in records]==ids
ass={int(a):(b,c) for a,b,c in (line.split('\t',2) for line in (L/'assessment.tsv').read_text().splitlines())};assert set(ass)==S
for x,d in zip(records,ds):
 a,p,ln=originals[d['mathdb_id']];assert x['record']==a
 assert d['literal_statement']==a['statement'];assert d['statement_sha256']==x['statement_sha256']==H(a['statement'].encode('utf-8'))
 assert d['canonical_record_sha256']==x['canonical_record_sha256']==H(json.dumps(a,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
 assert d['original_chunk']==x['original_chunk']==p and d['original_line']==x['original_line']==ln
 assert (d['disposition'],d['technical_assessment'])==ass[d['mathdb_id']];assert d['eligible_proposal'] is False
assert load(L/'proposals.json')==[]
ss=load(L/'source-catalogue.json');assert len(ss)==54
for s in ss:check(pathlib.Path(s['path']),s)
assert len(load(L/'bounded-checks.json')['orbits'])==10
print(json.dumps(dict(integrity='PASS',math_novelty='NOT_CERTIFIED',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=H((L/'manifest.json').read_bytes()),records=50,chunks=20,baseline_reported_reviews=2933,proposals=0,counts='9 additional / 39 total / next 40',scope='Independent byte/payload/original validation; no upstream verifier execution'),indent=2))
