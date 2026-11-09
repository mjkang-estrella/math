from pathlib import Path
import hashlib,json,shutil
L=Path(__file__).resolve().parent
B=L.parent.parent
W=L.parent/'sol-fullerene-heat-trace-breadth-depth-r286'
rows=[]
for p in W.rglob('*'):
 if p.is_file() and (p.parent==W or ('primary' in p.relative_to(W).parts and (p.name.startswith(('1910','1003','0902','fullerene','older','cospectral','pencil','successor','author','registry','openai')))) or (p.parent.name=='frozen' and 'fullerenes.' in p.name)) and p.suffix not in ['.py','.pyc']:
  q=L/'frozen'/p.relative_to(W);q.parent.mkdir(parents=True,exist_ok=True)
  a=p.read_bytes();h=hashlib.sha256(a).hexdigest();q.write_bytes(a)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
  rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':h,'bytes':len(a)})
for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
 p=B/name;q=L/'administrative'/name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
(L/'freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({'frozen':len(rows)}))
