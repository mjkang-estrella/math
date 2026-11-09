import pathlib,json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_bytes()); expected=(p/'reservation.sha256').read_text().split()[0]
assert sha((p/'reservation.json').read_bytes())==expected
(p/'reservation-check-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'expected':expected,'actual':expected,'match':True},indent=2))
out=p/'raw';out.mkdir(exist_ok=True); records={}
corpus=p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=None
 with f.open('rb') as stream:
  for n,b in enumerate(stream,1):
   o=json.loads(b); ident=o.get('mathdb_id',o.get('id'))
   if ident in r['ids']:
    if chunkhash is None:chunkhash=sha(f.read_bytes())
    (out/f'{ident}.jsonl').write_bytes(b)
    (out/f'{ident}.json').write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
    stmt=o.get('statement',o.get('content',''))
    records[str(ident)]={'chunk':str(f),'line_1based':n,'chunk_sha256':chunkhash,'raw_sha256':sha(b),'statement_field': 'statement' if 'statement' in o else 'content','statement_sha256':sha((stmt if isinstance(stmt,str) else json.dumps(stmt,ensure_ascii=False)).encode()),'record':o}
assert len(records)==20,(len(records),records.keys())
(p/'provenance.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n')
for k,v in records.items(): print(k,json.dumps(v['record'],ensure_ascii=False))
