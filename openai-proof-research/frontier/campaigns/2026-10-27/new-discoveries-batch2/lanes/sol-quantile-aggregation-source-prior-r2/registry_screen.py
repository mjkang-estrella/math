from pathlib import Path
import json,hashlib,re,datetime
L=Path(__file__).resolve().parent; B=L.parent
paths=[B/'sol-fresh-analysis-discovery-r7'/'sources'/n for n in ['openai-head.json','omega-head.json','count-head.json','current-CONTENTS.md','count-registry.json']]
rows=[]
for p in paths:
 if p.exists():rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
(L/'registry-head-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
terms=['2007.12338','quantile mixture','quantile-mixture','mafi.12323','mixability','aggregation set']
hits=[]
for entry in json.loads((L/'registry-freeze.json').read_text())['files']+rows:
 p=Path(entry['path']);s=p.read_text(errors='replace')
 if 'head.json' in p.name:print(p.name,s[:1500])
 for term in terms:
  for m in list(re.finditer(re.escape(term),s,re.I))[:15]:hits.append({'path':str(p),'term':term,'excerpt':s[max(0,m.start()-250):m.end()+700]})
(L/'registry-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'terms':terms,'hits':hits,'limit':'15 hits per term/file; indexes and historical excerpts only, not current-head clearance'},indent=2)+'\n')
print(json.dumps(hits,indent=2))
