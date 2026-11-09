from pathlib import Path
import json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_bytes()); expected=(p/'reservation.sha256').read_text().split()[0]
assert h((p/'reservation.json').read_bytes())==expected
(p/'reservation-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':expected,'verified':True},indent=2))
ids=set(r['ids']); found={};out=p/'records';out.mkdir(exist_ok=True)
corpus=p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=None
 with f.open('rb') as fh:
  for n,b in enumerate(fh,1):
   d=json.loads(b);i=d.get('mathdb_id',d.get('id'))
   if i not in ids:continue
   assert str(i) not in found
   if chunkhash is None:chunkhash=h(f.read_bytes())
   (out/f'{i}.raw.jsonl').write_bytes(b)
   (out/f'{i}.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
   found[str(i)]={'chunk':str(f),'line_1based':n,'chunk_sha256':chunkhash,'raw_sha256':h(b),'record':d}
assert len(found)==20,found.keys()
(p/'provenance.json').write_text(json.dumps(found,ensure_ascii=False,indent=2)+'\n')
for i in r['ids']:
 d=found[str(i)]['record'];print(i,json.dumps(d,ensure_ascii=False))
