from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent;ids=json.loads((L/'reservation.json').read_text())['ids'];hits={str(i):[] for i in ids}
for base in [L.parent,L.parent.parent/'lanes']:
 for p in base.glob('*/results.json'):
  if p.parent==L:continue
  try:x=json.loads(p.read_text())
  except Exception:continue
  s=json.dumps(x)
  for i in ids:
   if str(i) in s:
    entries=[(k,v) for k,v in x.items() if str(i) in json.dumps(v)] if isinstance(x,dict) else [('array',s[:200])]
    hits[str(i)].append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matching_keys':[k for k,v in entries],'contexts':[str(v)[:1400] for k,v in entries]})
(L/'historical-screen.json').write_text(json.dumps(hits,indent=2))
for i,h in hits.items():
 if h:print(i,json.dumps(h)[:2200])
