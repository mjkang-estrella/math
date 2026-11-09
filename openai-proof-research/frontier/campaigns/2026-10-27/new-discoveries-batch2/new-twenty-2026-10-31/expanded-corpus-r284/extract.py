import json,hashlib,resource,time,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
h=lambda x:hashlib.sha256(x).hexdigest()
expected=(p/'reservation.sha256').read_text().split()[0]; actual=h((p/'reservation.json').read_bytes());assert actual==expected
(p/'reservation-before.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),expected=expected,actual=actual,passed=True),indent=2))
ids=json.loads((p/'reservation.json').read_text())['ids']; found={}
corpus=p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
(p/'raw').mkdir(exist_ok=True)
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=None
 with f.open('rb') as stream:
  for n,line in enumerate(stream,1):
   r=json.loads(line); i=r.get('mathdb_id',r.get('id'))
   if i in ids:
    assert str(i) not in found
    if chunkhash is None:chunkhash=h(f.read_bytes())
    (p/'raw'/f'{i}.jsonl').write_bytes(line)
    found[str(i)]={'chunk':str(f),'one_based_line':n,'chunk_sha256':chunkhash,'raw_sha256':h(line),'raw_newline_preserved':line.endswith(b'\n'),'record':r}
assert set(found)==set(map(str,ids)),(ids,found.keys())
(p/'literal-records.json').write_text(json.dumps(found,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(found,indent=2,ensure_ascii=False))
(p/'extract-log.json').write_text(json.dumps({'script':str(Path(__file__).resolve()),'cpu_seconds':resource.getrusage(resource.RUSAGE_SELF).ru_utime,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'exit':'success','records':20},indent=2))
