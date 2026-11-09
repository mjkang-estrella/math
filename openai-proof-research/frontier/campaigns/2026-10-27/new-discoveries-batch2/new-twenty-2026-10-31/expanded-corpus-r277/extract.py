from pathlib import Path
import json,hashlib,resource,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_text()); expected=(p/'reservation.sha256').read_text().split()[0]
assert sha((p/'reservation.json').read_bytes())==expected
(p/'reservation-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sha256':expected,'pass':True},indent=2))
(p/'raw').mkdir(exist_ok=True);out={}
for f in sorted((p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 chunk=None
 for n,b in enumerate(f.open('rb'),1):
  rec=json.loads(b);id=rec.get('mathdb_id',rec.get('id'))
  if id in r['ids'] or str(id) in map(str,r['ids']):
   id=str(id);(p/'raw'/f'{id}.jsonl').write_bytes(b)
   if chunk is None:chunk=sha(f.read_bytes())
   out[id]={'chunk':str(f),'line_1based':n,'chunk_sha256':chunk,'raw_sha256':sha(b),'parsed':rec}
assert set(out)==set(map(str,r['ids'])),out.keys()
(p/'provenance.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
for id,entry in out.items():
 print(id,json.dumps(entry['parsed'],ensure_ascii=False))
print('RESOURCE',resource.getrusage(resource.RUSAGE_SELF))
