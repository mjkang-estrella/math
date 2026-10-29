from pathlib import Path
import json,hashlib,shutil,datetime
D=Path(__file__).parent; L=D.parent
out={}
for label,manifest in [('candidate',L/'root-chatterjee-triangle-review-freeze-r1/review-freeze.json'),('preliminary',L/'root-chatterjee-preliminary-adoption-r1/review-hashes.json')]:
 m=json.loads(manifest.read_text()); src=Path(m['source_lane']); rows=[]
 for p,h in m['files'].items():
  data=(src/p).read_bytes(); assert hashlib.sha256(data).hexdigest()==h,(label,p)
  target=D/'inputs'/label/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  rows.append({'path':p,'sha256':h})
 out[label]={'source':str(src),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'files':rows,'count':len(rows)}
(D/'freeze-before.json').write_text(json.dumps(out,indent=2))
for p in ['AGENTS.md','NEXT.md','ledger.json','prior-campaign-context.json','lanes/root-chatterjee-preliminary-adoption-r1/ADOPTION.json','lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json']:
 src=L.parent/p;tar=D/'context'/p;tar.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,tar)
shutil.copyfile(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',D/'helper_guard.py')
print({k:v['count'] for k,v in out.items()})
