from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent; B=L.parent.parent
files=[B/x for x in ['AGENTS.md','ledger.json','prior-campaign-context.json','NEXT.md','RESULTS.md']]
files += [B.parents[2]/'AGENTS.md']
for name in ['root-semigroup-r294-disposition','sol-permutation-semigroup-boundary-closure-r294']:
 p=B/'lanes'/name
 files += [x for x in p.iterdir() if x.is_file()]
 if name.startswith('sol-'):
  files += list((p/'sources').glob('*'))
  # Flatten historical original bindings, never copy a history directory.
  for index in ['bindings.json','source-bindings.json']:
   for row in json.loads((p/index).read_text()):
    q=Path(row.get('original',''))
    if q.is_file() and ('1609' in q.name or 'ugolini' in q.name): files.append(q)
out=[]
for i,p in enumerate(sorted(set(files))):
 if not p.is_file(): continue
 data=p.read_bytes(); h=hashlib.sha256(data).hexdigest(); q=L/'frozen'/('%03d-'%i+p.name)
 q.parent.mkdir(exist_ok=True);q.write_bytes(data)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 out.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=h,size=len(data)))
(L/'bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('frozen',len(out))
