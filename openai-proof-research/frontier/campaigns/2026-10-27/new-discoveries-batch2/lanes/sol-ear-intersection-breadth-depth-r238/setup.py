from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent; B=L.parent.parent; R=L.parent/'sol-inverse-kl-breadth-depth-r235'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for rel in ['discovery.md','SCOUTING.md','SUMMARY.md','FAILURES.md','checks.py','ear_solve.py','ear-solve.json','checks.json','provenance.json','source-chronology.json','primary/triangulations.pdf','primary/triangulations.txt']:
 p=R/rel; q=L/'frozen'/rel; q.parent.mkdir(parents=True,exist_ok=True); h=sha(p); shutil.copyfile(p,q); assert sha(p)==sha(q)==h; rows.append(dict(original=str(p),copy=str(q),sha256=h))
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 q=L/'administrative'/name; q.parent.mkdir(exist_ok=True); shutil.copyfile(B/name,q)
(L/'scientificbindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Frozen',len(rows)); print((L/'frozen/discovery.md').read_text()); print((L/'frozen/SCOUTING.md').read_text())
