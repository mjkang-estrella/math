import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; B=D.parent.parent; R=json.loads((D/'reservation.json').read_bytes()); h=lambda b:hashlib.sha256(b).hexdigest(); receipts=[]
for kind in ['prior_report_hashes','input_hashes']:
 for name,expected in R[kind].items():
  p=pathlib.Path(name);actual=h(p.read_bytes());mutable=p.name=='ledger.json';receipts.append(dict(kind=kind,path=name,expected=expected,actual=actual,match=actual==expected,mutable=mutable));assert actual==expected or mutable
old={}
for name in R['prior_report_hashes']:
 for x in json.loads(pathlib.Path(name).read_bytes()):
  if x['mathdb_id'] in R['ids']:old[str(x['mathdb_id'])]=x
assert len(old)==40
P=B/'lanes/pi-mathdb-full-corpus-inventory-r301'; M=json.loads((P/'manifest.json').read_bytes());bindings={x['path']:x['sha256'] for x in M['files']};records={}
for p in sorted((P/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 raw=p.read_bytes(); actual=h(raw); assert actual==bindings[str(p.relative_to(P))];receipts.append(dict(kind='corpus_chunk',path=str(p),sha256=actual,bytes=len(raw),match=True))
 for line_no,line in enumerate(raw.splitlines(keepends=True),1):
  x=json.loads(line)
  if x['mathdb_id'] not in R['ids']:continue
  i=str(x['mathdb_id']); (D/'raw'/f'{i}.jsonl').write_bytes(line); o=old[i]; statement=x['statement']; assert h(statement.encode())==o.get('literal_sha256',o.get('statement_sha256'))
  canonical=h(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()); assert canonical==o['canonical_record_sha256']; records[i]=dict(record=x,chunk=str(p),chunk_sha256=actual,line_one_based=line_no,raw_sha256=h(line),raw_bytes=len(line),statement_sha256=h(statement.encode()),inherited_canonical_record_sha256=o['canonical_record_sha256'],canonical_record_sha256=canonical)
assert set(records)==set(map(str,R['ids']))
(D/'inherited-dispositions.json').write_text(json.dumps(old,indent=2,ensure_ascii=False)+'\n');(D/'record-bindings.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n');(D/'input-verification.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),receipts=receipts),indent=2)+'\n');print('PASS: 40 raw lines, statement hashes, 20 corpus chunk hashes, immutable prior/input bindings; mutable ledger separately reported')
