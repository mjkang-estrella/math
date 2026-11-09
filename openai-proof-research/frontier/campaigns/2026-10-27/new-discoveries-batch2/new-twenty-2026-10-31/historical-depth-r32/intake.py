import pathlib,json,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(90,)*2);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=pathlib.Path(__file__).resolve().parent;b=p.parent.parent;r=json.loads((p/'reservation.json').read_text());h=lambda x:hashlib.sha256(x).hexdigest();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'prior':{},'chunks':{},'records':{},'context':{}}
rows=json.loads((p/'inherited-rows.json').read_text());(p/'raw').mkdir(exist_ok=True)
for f,expected in r['prior_report_hashes'].items():
 actual=h(pathlib.Path(f).read_bytes());assert actual==expected;receipt['prior'][f]=actual
for f,expected in r['input_hashes'].items():receipt['context'][f]={'expected':expected,'actual':h(pathlib.Path(f).read_bytes()),'mutable_administrative':f.endswith('ledger.json')}
corpus=b/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 # reserved IDs lie in these two previously bound chunks
 if f.name not in ['mathdb-normalized-chunk-0014.jsonl','mathdb-normalized-chunk-0015.jsonl']:continue
 data=f.read_bytes();expected_chunk={'mathdb-normalized-chunk-0014.jsonl':'5d12317791e9a1578acc1223028a8dc821a69c3f08bea3bc6ae08c816db5a6e8','mathdb-normalized-chunk-0015.jsonl':'c4d4c8a94f6c7342801e5de32836754789c13a8ee992171281b164e6994444a1'}[f.name];assert h(data)==expected_chunk;receipt['chunks'][str(f)]={'sha256':h(data),'bytes':len(data)}
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line);i=str(d.get('mathdb_id'))
  if i not in rows:continue
  (p/'raw'/f'{i}.jsonl').write_bytes(line)
  old=rows[i];statement=d['statement'];assert h(statement.encode())==old['statement_sha256']
  canonical=h(json.dumps(d,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode());assert canonical==old['canonical_record_sha256']
  if 'corpus_line_sha256' in old: assert h(line)==old['corpus_line_sha256'] or h(line.rstrip(b'\r\n'))==old['corpus_line_sha256']
  if 'corpus_ref' in old:assert n==old['corpus_ref']['line']
  if 'chunk_ref' in old:assert h(data)==old['chunk_ref']['sha256']
  receipt['records'][i]={'path':str(f),'one_based_line':n,'raw_with_newline_sha256':h(line),'raw_without_newline_sha256':h(line.rstrip(b'\r\n')),'statement_sha256':h(statement.encode()),'canonical_record_sha256':canonical,'literal_statement':statement,'source_url':d['source_url'],'documented_by_source_url':d.get('documented_by_source_url')}
assert set(receipt['records'])==set(map(str,r['ids']))
for f in [b/'ledger.json',b/'prior-campaign-context.json',p.parent/'ledger.json',b/'lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',b/'lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 receipt['context'][str(f)]={'sha256':h(f.read_bytes()),'read_kind':'administrative family/disposition context; no proof audit'}
(p/'intake-receipt.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n');print('PASS 40 exact statements/canonical records; byte-preserved raw lines; prior hashes verified')
