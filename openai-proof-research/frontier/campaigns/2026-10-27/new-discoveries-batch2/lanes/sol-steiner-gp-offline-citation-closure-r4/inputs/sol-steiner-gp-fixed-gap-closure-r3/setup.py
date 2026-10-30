from pathlib import Path
import json,hashlib,datetime,shutil
L=Path(__file__).resolve().parent; B=L.parent
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['root-r165-preliminary-freeze-r1','root-steiner-gp-source-review-adoption-r2']:
 f=B/name/'review-freeze.json'; d=json.loads(f.read_text()); dest=L/'copies'/name; dest.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(f,dest/'review-freeze.json')
 for i,x in enumerate(d['files']):
  p=Path(x['path']); assert p.stat().st_size==x['bytes'] and digest(p)==x['sha256'],str(p)
  q=dest/'payload'/p.relative_to(Path(d.get('root',str(B/'sol-steiner-gp-source-prior-review-r2'))));q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  assert digest(q)==x['sha256']; rows.append(dict(x,copy=str(q)))
 print(name,len(d['files']))
(L/'before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2))
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=B.parent/n;shutil.copyfile(p,L/('context-'+n))
print('verified copied',len(rows))
