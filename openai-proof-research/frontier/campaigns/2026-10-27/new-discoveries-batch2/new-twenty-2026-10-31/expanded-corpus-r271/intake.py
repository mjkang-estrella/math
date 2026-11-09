import json,hashlib,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_text());expected=(p/'reservation.sha256').read_text().split()[0];actual=h((p/'reservation.json').read_bytes());assert expected==actual,(expected,actual)
(p/'reservation-check-before.json').write_text(json.dumps({'expected':expected,'actual':actual,'pass':True,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())},indent=2))
ids=set(r['ids']);out={};(p/'raw').mkdir(exist_ok=True)
corpus=p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes()
 for ln,b in enumerate(data.splitlines(keepends=True),1):
  obj=json.loads(b);i=obj.get('id',obj.get('mathdb_id'))
  try:i=int(i)
  except:continue
  if i in ids:
   assert str(i) not in out
   (p/'raw'/f'{i}.jsonl').write_bytes(b)
   statement=obj.get('statement',obj.get('content',''))
   out[str(i)]={'chunk':str(f),'line_one_based':ln,'chunk_sha256':h(data),'raw_sha256':h(b),'statement_sha256':h(statement.encode() if isinstance(statement,str) else json.dumps(statement,ensure_ascii=False,sort_keys=True).encode()),'record':obj}
assert set(map(int,out))==ids,(ids-set(map(int,out)))
(p/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
for i in r['ids']:print(i,json.dumps(out[str(i)],ensure_ascii=False))
print('RESERVATION PASS',actual)
