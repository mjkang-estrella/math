from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]; B=L.parent; R=B.parent.parent.parent.parent.parent
paths=[]
for n in ['root-mathdb-breadth-intake-r350','root-mathdb-accepted-exclusions-r304','pi-mathdb-full-corpus-inventory-r301','pi-mathdb-primary-qualified-breadth-r351']:
 p=B/n
 if n.endswith('r350'): paths += [p/x for x in ['manifest.json','bindings.json','DECISION.md','coverage-delta.json','queue.json','reserved-ids.json']]
 elif n.endswith('r304'): paths += [p/x for x in ['manifest.json','accepted-exclusions.json','historical-dispositions.json','README.md']]
 elif n.endswith('r301'): paths += [p/'manifest.json']+sorted((p/'corpus').glob('*.jsonl'))
 else: paths += sorted(x for x in p.rglob('*') if x.is_file())
paths += [B.parent/x for x in ['ledger.json','prior-campaign-context.json']]
paths += [B.parents[4]/'sources'/x for x in ['upstream.json','CONTENTS.md']]
rows=[]
for p in paths:
 if not p.exists(): print('MISSING',p);continue
 b=p.read_bytes(); rows.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'input-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
for name in ['root-mathdb-breadth-intake-r350','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304']:
 p=B/name; m=json.loads((p/'manifest.json').read_text()); print(name, type(m).__name__)
 entries=m.get('files',[]) if isinstance(m,dict) else m
 if isinstance(entries,dict): print('dict schema',list(entries)[:2]);continue
 count=0
 for r in entries:
  rel=r.get('path',r.get('file')); q=p/rel
  if name.endswith('r301') and not rel.startswith('corpus/'):continue
  b=q.read_bytes(); assert len(b)==r.get('size',r.get('bytes')) and hashlib.sha256(b).hexdigest()==r['sha256'],q
  count+=1
 print('VALIDATED',count)
print('FROZEN',len(rows))
