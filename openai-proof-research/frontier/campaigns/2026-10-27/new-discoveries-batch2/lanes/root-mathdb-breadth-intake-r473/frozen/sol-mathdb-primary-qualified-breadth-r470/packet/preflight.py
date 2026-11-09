import pathlib,json,hashlib,datetime
R=pathlib.Path('/home/mj-kang/Documents/Dev/math');C=R/'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2';B=C/'lanes';L=B/'sol-mathdb-primary-qualified-breadth-r470'; failures=[];checks=[]; originals=[]
def sig(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return n,h.hexdigest()
def check(p,e,kind):
 try:
  n,h=sig(p);ok=h==e['sha256'] and n==e.get('bytes',e.get('size',n));checks.append(dict(path=str(p),kind=kind,ok=ok,bytes=n,sha256=h))
  if not ok:failures.append(str(p))
 except Exception as ex:failures.append(str(p)+': '+str(ex))
for name in ['root-mathdb-breadth-intake-r469','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363','pi-mathdb-full-corpus-inventory-r301']:
 d=B/name;m=json.loads((d/'manifest.json').read_text());rows=m if isinstance(m,list) else m['files']
 for e in rows:check(d/e['path'],e,'manifest')
 if name.startswith('pi-'):
  assert len(m['frozen_inputs'])==8
  assert sum(e['path'].startswith('corpus/mathdb-normalized-chunk-') for e in rows)==20
  for e in m['frozen_inputs']:check(d/e['path'],e,'inventory frozen_inputs')
 else:
  for e in json.loads((d/'bindings.json').read_text()):
   p=pathlib.Path(e['original']);n,h=sig(p);originals.append(dict(path=str(p.relative_to(R)),bytes=n,sha256=h));check(p,e,'actual original')
(L/'original-bindings.json').write_text(json.dumps(dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=originals),indent=2)+'\n')
(L/'preflight-checks.json').write_text(json.dumps(dict(checks=checks,failures=failures),indent=2)+'\n')
print('manifest/original checks',len(checks),'failures',len(failures));print('\n'.join(failures))
assert not failures
ids=json.loads((B/'root-mathdb-breadth-intake-r469/reserved-ids.json').read_text()); queue=json.loads((B/'root-mathdb-breadth-intake-r469/queue.json').read_text());cov=json.loads((B/'root-mathdb-breadth-intake-r469/coverage-delta.json').read_text());wanted=set(ids['ids']);assert len(wanted)==50 and wanted=={e['mathdb_id'] for e in queue}
assert not wanted.intersection(ids['other_active_reservations']) and not wanted.intersection(map(int,cov)) and not wanted.intersection({372627,372628,368940,404067,364119})
ex=json.loads((B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text());assert not wanted.intersection(map(int,ex['mathdb_lookup']))
hist=json.loads((B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text());histids=set()
def walk(v):
 if isinstance(v,dict):
  for k,x in v.items():
   if k in ('mathdb_id','problem_id') and str(x).isdigit():histids.add(int(x))
   else:walk(x)
 elif isinstance(v,list):
  for x in v:walk(x)
walk(hist);assert not wanted.intersection(histids)
records=[]
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for line,b in enumerate(p.open('rb'),1):
  d=json.loads(b)
  if d['mathdb_id'] in wanted:
   canonical=json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode();records.append(dict(record=d,original_chunk=str(p.relative_to(R)),original_line=line,original_line_sha256=hashlib.sha256(b).hexdigest(),canonical_record_sha256=hashlib.sha256(canonical).hexdigest(),statement_utf8_sha256=hashlib.sha256(d['statement'].encode()).hexdigest()))
assert len(records)==50
(L/'statements.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
with (L/'statements-read.txt').open('w') as f:
 for x in records:
  d=x['record'];f.write('\n## '+str(d['mathdb_id'])+' '+d['title']+'\n'+d['statement']+'\nSOURCE '+str(d['source_url'])+'\nREFERENCES '+str(d['references'])+'\n')
print('assignment PASS; baseline',len(cov),'statement reviews reported',sum(bool(v.get('record_statement_review')) for v in cov.values()));print('fifty extracted')
