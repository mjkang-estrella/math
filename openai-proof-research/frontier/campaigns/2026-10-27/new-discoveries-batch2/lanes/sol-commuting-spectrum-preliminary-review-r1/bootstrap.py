from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-wide-finite-source-scout-r256'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
paths=[p for p in S.iterdir() if p.is_file() and p.suffix in ('.md','.json','.jsonl','.log')]+[p for p in (S/'sources').iterdir() if p.is_file()]
for p in paths:
 q=L/'frozen'/p.relative_to(S);q.parent.mkdir(parents=True,exist_ok=True)
 h=digest(p);shutil.copyfile(p,q)
 assert h==digest(q)==digest(p)
 rows.append(dict(original=str(p),copy=str(q),sha256=h,bytes=p.stat().st_size))
for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']:
 if p.exists():
  q=L/'administrative'/('ancestor-AGENTS.md' if p==B.parents[3]/'AGENTS.md' else p.name)
  q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
(L/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Frozen',len(rows),'scientific inputs; administrative files snapshotted.')
