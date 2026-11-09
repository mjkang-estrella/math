from pathlib import Path
import json,hashlib,re
L=Path(__file__).parent
terms={'subsum':'cardinal function|subsum multiplic|1911.01206|2508.13016','entropy':'entropy power|Toscani|1208.1035','magnitude':'magnitude of a graph|Whitney twist|Leinster','covariogram':'covariogram|Galerne','rectangle':'rectangular peg|Hugelmeyer|Greene.{0,5}Lobb','hotspots':'hot spots|Burdzy|Werner','determinantal':'Lyons|determinantal.*coupling','gaussian':'Gaussian correlation|Royen'}
hits={k:[] for k in terms}; refs=[]
roots=[L.parent,L.parents[4]/'2026-10-08'/'lanes']
for root in roots:
 if not root.exists():continue
 for lane in root.iterdir():
  if not lane.is_dir() or lane==L:continue
  for name in ['SUMMARY.md','SCOUTING.md','discovery.md']:
   p=lane/name
   if not p.is_file() or p.stat().st_size>120000:continue
   d=p.read_bytes(); digest=hashlib.sha256(d).hexdigest() # bind before reading
   t=d.decode(errors='replace')
   matched=False
   for k,pat in terms.items():
    m=re.search(pat,t,re.I)
    if m:
     hits[k].append({'path':str(p.resolve()),'sha256':digest,'excerpt':t[max(0,m.start()-120):m.end()+240]});matched=True
   if matched:refs.append({'path':str(p.resolve()),'sha256':digest})
   assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
(L/'history-hits.json').write_text(json.dumps(hits,indent=2))
for k,v in hits.items():print(k,len(v),[Path(x['path']).parent.name for x in v[:8]])
