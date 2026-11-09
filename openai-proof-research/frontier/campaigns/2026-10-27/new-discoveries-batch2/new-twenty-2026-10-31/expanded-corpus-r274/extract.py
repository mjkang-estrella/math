import json,hashlib,datetime,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=(p/'reservation.json').read_bytes(); expected=(p/'reservation.sha256').read_text().split()[0]; assert sha(r)==expected
(p/'reservation-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'expected':expected,'actual':sha(r),'pass':True},indent=2))
ids=json.loads(r)['ids']; found={}
corpus=p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 hits=[]
 with f.open('rb') as stream:
  for n,line in enumerate(stream,1):
   row=json.loads(line); i=row.get('mathdb_id',row.get('id'))
   if i in ids or str(i) in list(map(str,ids)): hits.append((str(i),n,line,row))
 if hits:
  h=sha(f.read_bytes())
  for i,n,line,row in hits:
   (p/'evidence'/f'{i}.raw.jsonl').write_bytes(line)
   found[i]={'chunk':str(f),'line_one_based':n,'chunk_sha256':h,'raw_sha256':sha(line),'record':row}
assert set(found)==set(map(str,ids)), (found.keys(),ids)
for i in ids:
 a=found[str(i)]; row=a['record']; print(i,json.dumps(row,ensure_ascii=False))
(p/'literal-records.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
