import pathlib,json,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(60,)*2);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
o=pathlib.Path(__file__).parent;b=o.parents[1];inv=b/'lanes/pi-mathdb-full-corpus-inventory-r301';r=json.loads((o/'reservation.json').read_text());old={str(x['mathdb_id']):x for x in json.loads((o/'inherited-selected.json').read_text())};manifest=json.loads((inv/'manifest.json').read_text());expected={x['path']:x['sha256'] for x in manifest['files']};out={};chunks=[];(o/'raw').mkdir(exist_ok=True)
for p in sorted((inv/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes();h=hashlib.sha256(data).hexdigest();assert h==expected['corpus/'+p.name];chunks.append({'path':str(p.resolve()),'sha256':h})
 for n,line in enumerate(data.splitlines(keepends=True),1):
  x=json.loads(line);sid=str(x.get('id',x.get('mathdb_id')))
  if sid not in old:continue
  (o/'raw'/f'{sid}.jsonl').write_bytes(line);statement=x.get('statement',x.get('content'));prior=old[sid].get('literal_statement',old[sid].get('statement'));assert statement==prior,(sid,x.keys())
  out[sid]={'path':str(p.resolve()),'line_1based':n,'chunk_sha256':h,'raw_line_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(statement.encode()).hexdigest(),'literal_statement':statement}
assert set(out)==set(map(str,r['ids']));(o/'raw-record-bindings.json').write_text(json.dumps(out,indent=2)+'\n');(o/'chunk-verification.json').write_text(json.dumps(chunks,indent=2)+'\n');print('PASS',len(out),'records',len(chunks),'chunks; exact old literal statements match')
