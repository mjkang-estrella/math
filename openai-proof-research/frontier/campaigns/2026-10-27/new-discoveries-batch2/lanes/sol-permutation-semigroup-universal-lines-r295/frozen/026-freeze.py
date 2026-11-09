from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent
files=[B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B/'RESULTS.md']
for lane in ['root-semigroup-r293-disposition','sol-permutation-semigroup-breadth-depth-r293']:
 p=B/'lanes'/lane
 files += [f for f in p.iterdir() if f.is_file()]
 if lane.startswith('sol-'):
  files += [f for d in ['sources','administrative','frozen'] for f in (p/d).rglob('*') if f.is_file() and f.suffix in ['.txt','.json','.md','.py','.pdf']]
out=[]
for i,p in enumerate(sorted(set(files))):
 data=p.read_bytes(); h=hashlib.sha256(data).hexdigest(); q=L/'frozen'/('%04d-'%i+p.name);q.parent.mkdir(exist_ok=True);q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 out.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,size=len(data)))
(L/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print(len(out),'flat frozen bindings; original/copy verified')
