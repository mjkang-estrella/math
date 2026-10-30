import json,hashlib,datetime,shutil
from pathlib import Path
L=Path(__file__).resolve().parent
B=L.parent.parent
F=B/'lanes/root-r169-preliminary-freeze-r1/review-freeze.json'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for r in json.loads(F.read_text())['files']:
 p=Path(r['path']); assert h(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
 q=L/'inputs'/p.relative_to(B);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 assert h(q)==r['sha256'];records.append(dict(r,copy=str(q.relative_to(L))))
(L/'before.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),freeze_sha256=h(F),files=records),indent=2))
print('verified and copied',len(records))
