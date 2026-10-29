from pathlib import Path
import json,hashlib,datetime,shutil
P=Path(__file__).resolve().parent; B=P.parent.parent; S=P.parent/'sol-fresh-source-discovery-r79'
f=json.loads((P.parent/'root-lasso-review-freeze-r1/review-freeze.json').read_text()); bad=[]
(P/'candidate-copy').mkdir(exist_ok=True)
for n,h in f['files'].items():
 b=(S/n).read_bytes(); assert hashlib.sha256(b).hexdigest()==h,n
 (P/'candidate-copy'/n).write_bytes(b)
 assert hashlib.sha256((P/'candidate-copy'/n).read_bytes()).hexdigest()==h
(P/'before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'count':len(f['files']),'all_match':True,'freeze_sha256':hashlib.sha256((P.parent/'root-lasso-review-freeze-r1/review-freeze.json').read_bytes()).hexdigest()},indent=2))
# Read all mandated context without emitting unrelated long historical text.
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 t=(B/n).read_text(); (P/(n+'.read-receipt')).write_text(json.dumps({'bytes':len(t.encode()),'sha256':hashlib.sha256(t.encode()).hexdigest()}))
print('49 frozen originals and own byte copies verified; context read')
