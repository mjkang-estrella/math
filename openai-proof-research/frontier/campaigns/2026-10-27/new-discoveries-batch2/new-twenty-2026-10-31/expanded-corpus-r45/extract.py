import pathlib,json,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(60,60));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
O=pathlib.Path(__file__).resolve().parent;B=O.parents[1];ids=set(json.load(open(O/'reservation.json'))['ids']);(O/'raw').mkdir(exist_ok=True);out={}
for f in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes();ch=hashlib.sha256(data).hexdigest()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line)
  if d['mathdb_id'] in ids:
   i=d['mathdb_id'];(O/'raw'/f'{i}.jsonl').write_bytes(line);out[str(i)]={'record':d,'chunk':str(f.resolve()),'one_based_line':n,'chunk_sha256':ch,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(d['statement'].encode()).hexdigest()}
assert len(out)==40
(O/'extracted.json').write_text(json.dumps(out,indent=2))
