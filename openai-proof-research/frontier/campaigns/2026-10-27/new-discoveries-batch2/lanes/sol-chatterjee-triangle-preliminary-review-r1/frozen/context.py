from pathlib import Path
import re,json,hashlib,datetime
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); P=Path(__file__).parent
files=[p for p in R.rglob('*') if p.is_file() and any(s in p.name.lower() for s in ['summary','discovery','findings','proof','review','ledger']) and P not in p.parents]
pat=re.compile(r'Chatterjee|Giacchini|cgk25|2609[.-]28707|boundary.contact|2511[.-]11901|Drach|Tatarko|Alzer.Berg',re.I)
hits=[]; inv=[]
for p in files:
 b=p.read_bytes(); inv.append({'path':str(p.relative_to(R)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 for i,l in enumerate(b.decode(errors='replace').splitlines(),1):
  if pat.search(l): hits.append({'path':str(p.relative_to(R)),'line':i,'text':l[:2400]})
(P/'report-inventory.json').write_text(json.dumps(inv,indent=2))
(P/'duplicate-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(files),'pattern':pat.pattern,'hits':hits},indent=2))
ctx={}
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/NEXT.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']:
 p=R/rel;b=p.read_bytes();ctx[rel]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
(P/'context.json').write_text(json.dumps(ctx,indent=2));print('files',len(files),'hits',len(hits)); print(json.dumps(hits,indent=2)[:20000])
