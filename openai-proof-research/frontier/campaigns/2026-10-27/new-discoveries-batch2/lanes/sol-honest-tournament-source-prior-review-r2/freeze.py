from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent
rows=[]
def bind(p,copy=False,admin=False):
 b=p.read_bytes(); h=hashlib.sha256(b).hexdigest(); dest=None
 if copy:
  d=L/('administrative' if admin else 'frozen')/p.parent.name/p.name;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b);assert hashlib.sha256(d.read_bytes()).hexdigest()==h;dest=str(d.relative_to(L))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 rows.append(dict(original=str(p),sha256=h,bytes=len(b),copy=dest,administrative=admin))
for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:bind(B/n,True,True)
P=L.parent/'sol-honest-tournament-preliminary-review-r1'
for n in ['review.md','access.jsonl','bindings.json','final-manifest.json','final-verification.json']:bind(P/n,True)
for n in ['STATUS.md','PROOF-reviewed.md']:bind(L.parent/'root-tournament-investment-r2'/n,True)
# Retain references to actual primary bodies already frozen; no historical tree copies.
for folder in ['frozen','current']:
 for p in sorted((P/folder).rglob('*')):
  if p.is_file():bind(p)
(L/'bindings.json').write_text(json.dumps(dict(frozen_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),inputs=rows),indent=2)+'\n')
print(json.dumps(rows,indent=2))
