import resource, pathlib, json, hashlib, datetime, time
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
start=time.monotonic(); P=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=P/'reservation.json'; expected=(P/'reservation.sha256').read_text().strip(); assert sha(r.read_bytes())==expected
ids=json.loads(r.read_text())['ids']; out={}; inventory=[]
corpus=P.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
(P/'raw').mkdir(exist_ok=True)
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 b=f.read_bytes(); h=sha(b)
 for n,line in enumerate(b.splitlines(keepends=True),1):
  obj=json.loads(line); mid=obj.get('mathdb_id',obj.get('id'))
  if mid is not None and int(mid) in ids:
   mid=int(mid); assert str(mid) not in out
   (P/'raw'/f'{mid}.jsonl').write_bytes(line)
   out[str(mid)]={'raw_provenance':{'chunk':str(f),'one_based_line':n,'chunk_sha256':h,'raw_sha256':sha(line),'newline_preserved':line.endswith(b'\n')},'record':obj}
 inventory.append({'path':str(f),'sha256':h})
 assert time.monotonic()-start<135
assert set(out)==set(map(str,ids)),(len(out),corpus)
(P/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
(P/'extraction-log.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reservation_before':expected,'chunks':inventory,'seconds':time.monotonic()-start,'script':str(P/'extract.py'),'cpu_limit':120,'wall_limit':140,'as_bytes':6*1024**3},indent=2)+'\n')
for k,v in out.items():
 print(k,json.dumps(v['record'],ensure_ascii=False))
