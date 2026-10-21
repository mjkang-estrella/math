import json,hashlib,urllib.request
from pathlib import Path
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r118/packet'
t=json.loads((ROOT/'sources/preprints-tree.json').read_bytes())
prefix='preprints/Milnes-rationality-conjecture-for-abelian-varieties-October-7-2026/'
rows=[]
for e in t['tree']:
 if e['path'].startswith(prefix) and e['path'].endswith('.tex'):
  url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
  b=urllib.request.urlopen(url,timeout=45).read();sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==e['size'] and sha==e['sha']
  dst='private/source/'+e['path'][len(prefix):];p=OUT/dst;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
  rows.append({'canonical_path':e['path'],'path':dst,'size':len(b),'git_blob':sha,'sha256':hashlib.sha256(b).hexdigest(),'url':url})
(OUT/'source-identities.json').write_text(json.dumps(rows,indent=2))
print('Authenticated',len(rows),'tex sources')
