from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
def freeze(p, dest):
 dest.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p); shutil.copyfile(p,dest)
 assert h==sha(p)==sha(dest)
 records.append(dict(original=str(p),copy=str(dest.relative_to(L)),sha256=h))
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 freeze(B/name,L/'administrative'/name)
freeze(B.parents[3]/'AGENTS.md',L/'administrative'/'ancestor-AGENTS.md')
freeze(L.parent/'root-fullerene-vertices-disposition-r5'/'STATUS.md',L/'frozen'/'root-STATUS.md')
P=L.parent/'sol-fullerene-vertices-hulls-formal-r2'
for p in sorted(P.iterdir()):
 if p.is_file(): freeze(p,L/'frozen'/'hulls'/p.name)
(L/'source-bindings.json').write_text(json.dumps(records,indent=2)+'\n')
print(len(records),'sources frozen and hashes matched')
