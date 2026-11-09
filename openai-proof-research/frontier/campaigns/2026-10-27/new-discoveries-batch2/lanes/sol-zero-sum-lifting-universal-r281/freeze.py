from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent; R=B.parents[3]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
items=[]
def bind(p,kind,copy=False):
 a=h(p); q=None
 if copy:
  q=L/'administrative'/((p.parent.name+'-')+p.name);q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q);assert h(q)==a
 assert h(p)==a
 items.append(dict(path=str(p),sha256=a,kind=kind,copy=str(q) if q else None))
for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']:
 if p.exists():bind(p,'administrative snapshot',True)
old=L.parent/'sol-wide-discrete-algebraic-certificates-r277'
for p in old.iterdir():
 if p.is_file():bind(p,'immutable prior lane reference')
for p in (old/'sources').iterdir():
 if p.is_file():bind(p,'immutable scientific source')
bind(L.parent/'root-scout-r277-disposition/STATUS.md','root disposition')
for name in ['upstream.json','CONTENTS.md','preprints-tree.json']:
 p=R/'sources'/name
 if p.exists():bind(p,'immutable registry reference')
(L/'source-bindings.json').write_text(json.dumps({'frozen_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'bindings':items},indent=2))
print('Frozen',len(items),'files before scientific reading; immutable references reused.')
