from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
def bind(p,admin=False):
 rel=p.relative_to(B) if p.is_relative_to(B) else Path('ancestor')/p.name
 dest=L/('administrative' if admin else 'frozen')/rel
 dest.parent.mkdir(parents=True,exist_ok=True)
 a=sha(p); dest.write_bytes(p.read_bytes()); assert a==sha(p)==sha(dest)
 records.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=a,administrative=admin))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:bind(B/name,True)
bind(B.parents[3]/'AGENTS.md',True)
for lane in ['sol-super-coupon-source-prior-breadth-r2','sol-dependent-super-coupon-preliminary-review-r1','sol-wide-analytic-source-scout-r254']:
 root=B/'lanes'/lane
 for p in root.iterdir():
  if p.is_file() and p.suffix in ['.md','.json']:bind(p)
 for sub in ['texts','retrieved','primary','frozen-live']:
  d=root/sub
  if d.exists():
   for p in d.rglob('*'):
    if p.is_file() and p.suffix in ['.txt','.pdf','.json','.html','.md'] and p.stat().st_size<15000000:bind(p)
(L/'bindings.json').write_text(json.dumps({'frozen_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':records},indent=2))
print(len(records),'files bound; scientific reading may begin')
