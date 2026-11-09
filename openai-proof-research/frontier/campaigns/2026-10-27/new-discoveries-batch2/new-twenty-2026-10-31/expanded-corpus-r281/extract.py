import json,hashlib,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent; res=json.loads((p/'reservation.json').read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha((p/'reservation.json').read_bytes())==(p/'reservation.sha256').read_text().split()[0]
ids=set(res['ids']); out={}; (p/'raw').mkdir(exist_ok=True)
for f in sorted((p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  r=json.loads(line); i=r.get('mathdb_id',r.get('id'))
  if i not in ids: continue
  (p/'raw'/f'{i}.jsonl').write_bytes(line)
  out[str(i)]={'chunk':str(f),'line':n,'chunk_sha256':sha(data),'raw_sha256':sha(line),'record':r}
assert len(out)==20,(len(out),out.keys())
(p/'raw-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for i in res['ids']:
 print('\nID',i,json.dumps(out[str(i)]['record'],ensure_ascii=False))
print('EXTRACTION COMPLETE',len(out))
