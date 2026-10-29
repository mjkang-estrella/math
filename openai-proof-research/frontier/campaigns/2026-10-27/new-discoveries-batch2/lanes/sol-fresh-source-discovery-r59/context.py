from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent;C=P.parent.parent;R=C.parents[3]
paths=[C/'AGENTS.md',C/'NEXT.md',C/'ledger.json',C/'prior-campaign-context.json',R/'AGENTS.md']
rows=[]
for p in paths:
 data=p.read_bytes();r={'path':str(p),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
 if p.suffix=='.json':
  d=json.loads(data);r['top_keys']=list(d)
  r['scope_entries']=[{'section':k,'title':v.get('title'), 'path':v.get('path'),'source':v.get('source_target'),'status':v.get('status')} for k,vs in d.items() if isinstance(vs,list) for v in vs if isinstance(v,dict)]
 rows.append(r)
for n in ['sol-fresh-source-discovery-r56','sol-fresh-source-discovery-r57','sol-fresh-source-discovery-r58']:
 p=P.parent/n/'SUMMARY.md';rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'text':p.read_text()})
(P/'context-screen.json').write_text(json.dumps(rows,indent=2)+'\n');print('context files',len(rows))
