from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
S=L.parent/'sol-floor-sums-certificate-r2'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(S.rglob('*')):
 if not p.is_file():continue
 q=L/'frozen'/p.relative_to(S)
 q.parent.mkdir(parents=True,exist_ok=True)
 h=digest(p);shutil.copyfile(p,q)
 assert digest(p)==h==digest(q)
 rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,bytes=p.stat().st_size))
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
for n in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 q=L/'administrative'/n;q.parent.mkdir(exist_ok=True);shutil.copyfile(B/n,q)
print(json.dumps({'frozen_files':len(rows),'bytes':sum(x['bytes'] for x in rows)}))
