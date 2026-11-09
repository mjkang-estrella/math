from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r549'
def meta(p):
 b=p.read_bytes(); return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
def check(p,e):
 a=meta(p); assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p); return a
out=[meta(I/'manifest.json'),meta(I/'verification-receipt.json')]
m=json.loads((I/'manifest.json').read_bytes())
assert set(str(p.relative_to(I)) for p in I.rglob('*') if p.is_file())=={x['path'] for x in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:out.append(check(I/e['path'],e))
for e in json.loads((I/'bindings.json').read_bytes()):
 out.extend([check(Path(e['original']),e),check(Path(e['copy']),e)])
p=L/'pi-mathdb-full-corpus-inventory-r301/manifest.json'; out.append(meta(p))
# Inspect only structure after the intake-bound manifest original/copy check.
r=json.loads(p.read_bytes()); print('inventory keys',list(r))
for k,v in r.items():
 if isinstance(v,list) and v:print(k,len(v),str(v[0])[:700])
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('intake bound',len(out))
chunks=[e for e in r['files'] if e['path'].startswith('corpus/') and e['path'].endswith('.jsonl')]
print('chunks',len(chunks),[e['path'] for e in chunks]); assert len(chunks)==20
for e in chunks+r['frozen_inputs']:out.append(check(p.parent/e['path'],e))
# Bind required campaign/prior references before reading.
extra=[L.parent/'ledger.json',L.parent/'prior-campaign-context.json',L.parents[4]/'sources/upstream.json',L.parents[4]/'sources/CONTENTS.md']
for root in ['root-mathdb-breadth-intake-r304','root-mathdb-breadth-intake-r363']:
 for q in (L/root).glob('*'):
  if q.is_file():out.append(meta(q))
for q in extra:
 if q.exists():out.append(meta(q))
(D/'flat-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for name in ['queue.json','reserved-ids.json','active-breadth-reservations.json']:
 v=json.loads((I/name).read_bytes());print(name,str(v)[:2500])
print('coverage shape',str(json.loads((I/'coverage-delta.json').read_bytes()))[:1200])
