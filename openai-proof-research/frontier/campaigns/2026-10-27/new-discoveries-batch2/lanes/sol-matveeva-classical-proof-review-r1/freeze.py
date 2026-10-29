from pathlib import Path
import json,hashlib
b=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
o=b/'lanes/sol-matveeva-classical-proof-review-r1'
f=b/'lanes/root-fresh-source-r100-r101-handbacks/r100-freeze.json'
j=json.loads(f.read_text()); src=Path(j['source_lane']); rows=[]
for p,h in j['files'].items():
 data=(src/p).read_bytes(); actual=hashlib.sha256(data).hexdigest(); assert actual==h,p
 dest=o/'inputs/r100'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);rows.append({'path':p,'sha256':actual})
(o/'inputs/r100-freeze.json').write_bytes(f.read_bytes())
(o/'freeze-before.json').write_text(json.dumps({'verified':len(rows),'files':rows},indent=2))
print('verified and byte-copied',len(rows))
