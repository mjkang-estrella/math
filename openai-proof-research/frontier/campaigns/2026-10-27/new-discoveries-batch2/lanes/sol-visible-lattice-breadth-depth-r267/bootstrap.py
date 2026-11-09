from pathlib import Path
import hashlib,json,shutil,datetime
L=Path(__file__).resolve().parent
B=L.parent.parent
items=[]
def bind(p,category):
 p=Path(p); raw=p.read_bytes(); h=hashlib.sha256(raw).hexdigest()
 out=L/category/p.parent.name/p.name; out.parent.mkdir(parents=True,exist_ok=True); out.write_bytes(raw)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(out.read_bytes()).hexdigest()
 items.append(dict(original=str(p),copy=str(out.relative_to(L)),sha256=h,category=category))
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:bind(B/name,'admin')
for name in ['PROOF.md','check.py','1909.02634v1.pdf','1909.02634v1.txt']:bind(L.parent/'root-quasi-distance-grid-r1'/name,'frozen')
R=L.parent/'sol-wide-cross-family-mechanisms-r263'
for name in ['SCOUTING.md','SUMMARY.md','discovery.md','visible-prior.xml','visible-prior.json','bindings.jsonl','retrieval.jsonl']:bind(R/name,'frozen')
for p in (R/'sources').iterdir():
 if p.is_file():bind(p,'frozen')
(L/'bindings.json').write_text(json.dumps(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),items=items),indent=2))
print('Bound',len(items),'files before scientific reading')
