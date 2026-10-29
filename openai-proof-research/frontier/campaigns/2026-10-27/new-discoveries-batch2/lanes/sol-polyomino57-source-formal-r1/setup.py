from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
f=json.loads((B/'lanes/root-polyomino-preliminary-r1/freeze.json').read_text())
r=[]
for e in f['files']:
 p=Path(e['path']); assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 q=L/'input'/p.relative_to(B); q.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(p,q)
 r.append(dict(e,copy=str(q)))
for n in ['freeze.json','INVESTMENT.json','ROOT-NOTES.json']:
 shutil.copy2(B/'lanes/root-polyomino-preliminary-r1'/n,L/n)
shutil.copy2(B/'candidates/log-arctangent-mean/pins.json',L/'pins.json')
(L/'hash-before.json').write_text(json.dumps(r,indent=2))
