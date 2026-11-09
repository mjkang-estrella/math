from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent;R=L.parent
jobs=[['leanpool-head.json','https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD'],['openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD']]
for x in json.loads((L/'reservation.json').read_text())['rows']:
 aid=x['source_url'].split('/')[-1]
 for suffix,url in [('abs.html','https://arxiv.org/abs/'+aid),('pdf','https://arxiv.org/pdf/'+aid)]:
  pair=[aid+'.'+suffix,url]
  if pair not in jobs:jobs.append(pair)
(L/'jobs.json').write_text(json.dumps(jobs))
# Read inherited evidence, hash complete inputs; extract relevant family matches.
inputs=[R/'ledger.json',R.parent/'ledger.json',R.parent/'prior-campaign-context.json',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]
manifest=[]
for p in inputs:
 if p.exists():
  b=p.read_bytes();manifest.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
(L/'inherited-inputs.json').write_text(json.dumps(manifest,indent=2))
