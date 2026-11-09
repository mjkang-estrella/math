import pathlib,json,hashlib,datetime,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent
H=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
r=json.loads((L/'reservation.json').read_text()); receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'immutable':[],'mutable':[]}
for k in ['prior_report_hashes','input_hashes']:
 for p,h in r[k].items():
  actual=H(p);v={'path':p,'expected':h,'actual':actual,'match':h==actual}
  receipt['mutable' if p.endswith('/ledger.json') else 'immutable'].append(v)
  if not p.endswith('/ledger.json'):assert h==actual,v
old={}
for p in r['prior_report_hashes']:
 for x in json.loads(pathlib.Path(p).read_text()):
  if x['mathdb_id'] in r['ids']:old[str(x['mathdb_id'])]=x
assert len(old)==40
I=B/'lanes/pi-mathdb-full-corpus-inventory-r301';m=json.loads((I/'manifest.json').read_text());chunks={}
for v in m['files']:
 if v['path'].startswith('corpus/mathdb-normalized-chunk-'):
  p=I/v['path'];assert H(p)==v['sha256'];chunks[str(p)]={'sha256':H(p),'bytes':p.stat().st_size}
(L/'raw').mkdir(exist_ok=True)
results={}
for id,x in old.items():
 ref=x.get('corpus_ref',{'path':x.get('corpus_path'),'line':x.get('corpus_line')});p=pathlib.Path(ref['path']);raw=p.read_bytes().splitlines(keepends=True)[ref['line']-1];obj=json.loads(raw)
 canon=json.dumps(obj,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode();assert hashlib.sha256(canon).hexdigest()==x['canonical_record_sha256'],id
 (L/'raw'/f'{id}.jsonl').write_bytes(raw)
 assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['statement_sha256']
 results[id]={'mathdb_id':int(id),'title':next(z['title'] for z in r['rows'] if z['mathdb_id']==int(id)),'old_disposition':x['disposition'],'old_report':r['prior_coverage'][id]['report'],'old_report_sha256':next(h for p,h in r['prior_report_hashes'].items() if r['prior_coverage'][id]['report'] in p),'inherited_objection':x.get('concrete_reason',x.get('reason')),'old_disposition_verbatim':x,'literal_statement':x['literal_statement'],'source_url':x['source_url'],'raw_binding':{'path':str(p),'line_one_based':ref['line'],'chunk_sha256':chunks[str(p)]['sha256'],'raw_line_with_newline_sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'terminal_newline':raw.endswith(b'\n'),'canonical_record_sha256':x['canonical_record_sha256']},'new_outcome':'RETAIN_INHERITED_HOLD_NO_NEW_PRIMARY_BODY','new_primary_body_review':False,'new_proof_body_review':False,'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0,'new_unique_coverage_credit':0,'remaining_lemma_or_gap':x.get('concrete_reason',x.get('reason'))}
(L/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n');(L/'intake-receipt.json').write_text(json.dumps(receipt|{'verified_chunks':chunks,'raw_count':len(results)},indent=2)+'\n')
print('40 bound reports and exact raw rows verified; all 20 chunks verified. Mutable ledger differences separately recorded.')
