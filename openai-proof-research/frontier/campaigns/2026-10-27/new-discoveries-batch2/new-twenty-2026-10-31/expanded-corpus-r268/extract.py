from pathlib import Path
import json,hashlib,resource,datetime,time
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((p/'reservation.json').read_bytes()); assert sha((p/'reservation.json').read_bytes())==(p/'reservation.sha256').read_text().split()[0]
(p/'raw').mkdir(exist_ok=True); out={}
c=p.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(c.glob('mathdb-normalized-chunk-*.jsonl')):
 for n,b in enumerate(f.open('rb'),1):
  d=json.loads(b);i=d.get('mathdb_id')
  if i in r['ids']:
   assert str(i) not in out
   (p/'raw'/f'{i}.jsonl').write_bytes(b)
   out[str(i)]={'record':d,'provenance':{'chunk':str(f),'one_based_line':n,'chunk_sha256':sha(f.read_bytes()),'raw_sha256':sha(b),'statement_sha256_utf8':sha(d['statement'].encode()),'newline_preserved':b.endswith(b'\n')}}
assert set(map(int,out))==set(r['ids'])
(p/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
(p/'reservation-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'actual':sha((p/'reservation.json').read_bytes()),'expected':(p/'reservation.sha256').read_text().split()[0],'ids':r['ids'],'pass':True},indent=2)+'\n')
for i in r['ids']:
 d=out[str(i)]['record'];print('\n',i,d['title'],'\nSOURCE',d['source_url'],'\n',d['statement'],'\nREFERENCES',d['references'])
print('JOB completed; CPU',time.process_time(),'maxrss',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
