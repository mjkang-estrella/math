"""Final exact membership seal; refuses to overwrite a manifest. Writes own root only."""
from pathlib import Path
import json,hashlib
from verify import inventory,digest,ENVELOPES
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r158')
if (R/'MANIFEST.json').exists(): raise RuntimeError('already sealed')
old=json.loads((R/'private/incoming-original-identities.json').read_text())['originals']
for x in old:
 b=Path(x['incoming_original']).read_bytes()
 assert len(b)==x['size'] and hashlib.sha256(b).hexdigest()==x['sha256']
(R/'private/originals-recheck.json').write_text(json.dumps({'count':len(old),'result':'eleven named original files still match late-capture identities','scope':'not a snapshot of entire old roots'},indent=2)+'\n')
files,dirs=inventory(R)
manifest={'schema':'r158-exact-payload-v1','envelopes':list(ENVELOPES),'files':{k:v for k,v in files.items() if k not in ENVELOPES},'directories':dirs,'scope':'bytes/exact membership; no modes or mathematical gates'}
(R/'MANIFEST.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print(json.dumps({'payload_files':len(manifest['files']),'directories':len(dirs),'detached_anchors':{n:digest(R/n) for n in ENVELOPES}},indent=2))
