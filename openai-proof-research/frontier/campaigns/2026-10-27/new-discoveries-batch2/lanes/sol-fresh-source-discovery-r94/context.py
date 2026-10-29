from pathlib import Path
import re,json,hashlib
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); lane=Path(__file__).parent
files=[p for p in root.rglob('*') if p.is_file() and p.suffix in ['.md','.json'] and any(s in p.name.lower() for s in ['summary','discovery','findings','proof','review','ledger']) and lane not in p.parents]
pat=re.compile(r'Ball.?Nayar|Lamkin|2609\.11418|2608\.00813|1509\.05926|2308\.15997|entropy concavity|revent2|mom-ave',re.I)
hits=[]
for p in files:
 for i,l in enumerate(p.read_text(errors='replace').splitlines(),1):
  if pat.search(l):hits.append({'file':str(p.relative_to(root)),'line':i,'text':l[:1800]})
(lane/'report-inventory.txt').write_text('\n'.join(str(p.relative_to(root)) for p in files)+'\n')
(lane/'duplicate-screen.json').write_text(json.dumps({'files':len(files),'pattern':pat.pattern,'hits':hits},indent=2))
ctx={}
for rel in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json','frontier/campaigns/2026-10-27/new-discoveries-batch2/NEXT.md','frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json']:
 p=root/rel;b=p.read_bytes();ctx[rel]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
(lane/'context.json').write_text(json.dumps(ctx,indent=2));print('files',len(files),'hits',len(hits));print(json.dumps(hits[:12],indent=2))
