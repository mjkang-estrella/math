from pathlib import Path
import json,hashlib,sys,subprocess,xml.etree.ElementTree as ET
L=Path(__file__).resolve().parent
terms=['Hildebrand','occupancy fraction','Dombi','Hendrickson','periodic tiling','Gilmer','directed KKL','pseudo 2-factor','diperfect','Aharoni and Korman','Gerbner','annihilation number','stable Kneser','triangle-free induced']
files=sorted(p for p in L.parent.glob('*/*') if p.is_file() and p.name in ['SCOUTING.md','SUMMARY.md','STATUS.md','discovery.md'] and p.parent!=L)
bindings=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files]
(L/'history-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
out={t:[] for t in terms}
for p,b in zip(files,bindings):
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==b['sha256']
 for t in terms:
  hits=[s for s in data.decode(errors='replace').splitlines() if t.lower() in s.lower()]
  if hits:out[t].append(dict(path=str(p),hits=hits))
(L/'dedup.json').write_text(json.dumps(out,indent=2)+'\n')
for t,hs in out.items():print(t,[(Path(x['path']).parent.name) for x in hs])
