from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parents[1]; B=L.parent
paths=[]; reports=[]
def h(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
for name in ['root-mathdb-breadth-intake-r355','root-mathdb-accepted-exclusions-r304','pi-mathdb-full-corpus-inventory-r301']:
 p=B/name; paths.append(p/'manifest.json'); m=json.loads((p/'manifest.json').read_text()); entries=m['files'] if isinstance(m,dict) else m; count=0
 if isinstance(entries,dict): raise ValueError('unexpected manifest schema')
 for e in entries:
  s=e['path']
  if name.endswith('r301') and not s.startswith('corpus/'):continue
  q=p/s; r=h(q); assert r['size']==e.get('size',e.get('bytes',r['size'])) and r['sha256']==e['sha256'],q
  paths.append(q); count+=1
 if name.endswith('r301'): assert count==20
 if name.endswith('r355'):
  actual={str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}-{'manifest.json','verification-receipt.json'}
  assert actual=={e['path'] for e in entries}
 reports.append({'manifest':str(p/'manifest.json'),'checked_entries':count})
# Flat references, never recursive copies. Bind originals underlying root intake as well.
for e in json.loads((B/'root-mathdb-breadth-intake-r355/bindings.json').read_text()):
 q=Path(e['original']); r=h(q);assert r['sha256']==e['sha256'] and r['size']==e['size'],q
 paths.append(q)
for n in ['ledger.json','prior-campaign-context.json']: paths.append(B.parent/n)
repo=B.parents[5]
for n in ['upstream.json','CONTENTS.md']: paths.append(repo/'sources'/n)
paths=[p for p in paths if p.exists()]
rows=[h(p) for p in sorted(set(paths))]
(L/'input-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verified':reports,'flat_original_refs':len(rows),'scientific_content_read_before_freeze':False},indent=2)+'\n')
print(json.dumps(reports));print('BOUND',len(rows))
