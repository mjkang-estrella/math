from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent;B=L.parent.parent
rows=[];text=[]
for d in sorted((B/'lanes').iterdir()):
 if d==L:continue
 for name in ['SUMMARY.md','SCOUTING.md','discovery.md','summary.md']:
  p=d/name
  if not p.is_file():continue
  data=p.read_bytes()
  if len(data)>200000:continue
  h=hashlib.sha256(data).hexdigest()
  # Nonrecursive immutable references; verify before and after bounded inspection.
  s=data.decode(errors='replace');text.append('\nFILE '+str(p)+'\n'+s)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  rows.append({'path':str(p),'sha256':h})
(L/'history-bindings.json').write_text(json.dumps(rows,indent=2))
(L/'history-index.txt').write_text('\n'.join(text))
print(len(rows),'immediate historical artifacts indexed; no recursive trees')
