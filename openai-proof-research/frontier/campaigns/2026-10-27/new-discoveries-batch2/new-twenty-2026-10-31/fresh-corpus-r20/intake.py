import os,resource,json,hashlib,pathlib
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(40,40));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
p=pathlib.Path(__file__).resolve().parent;b=p.parent.parent
ids=set(json.loads((p/'reservation.json').read_text())['ids']);out={};(p/'literal').mkdir(exist_ok=True)
for f in sorted((b/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes();sha=hashlib.sha256(data).hexdigest()
 for i,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line);id=d.get('mathdb_id',d.get('id'))
  if id in ids:
   assert str(id) not in out
   (p/f'literal/{id}.jsonl').write_bytes(line)
   out[str(id)]={'chunk':str(f),'chunk_sha256':sha,'line':i,'raw_sha256':hashlib.sha256(line).hexdigest(),'newline':line.endswith(b'\n'),'record':d}
assert len(out)==35
(p/'literal-index.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
with (p/'literal-statements.txt').open('w') as w:
 for id,v in out.items():
  w.write('\nID '+id+'\n'+json.dumps(v['record'],ensure_ascii=False)+'\n')
print((p/'literal-statements.txt').read_text())
