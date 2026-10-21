import json,hashlib,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; PROJECT=ROOT.parents[3]
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=(PROJECT/'sources/preprints-tree.json').read_bytes()
assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b); assert len(t['tree'])==13223 and not t['truncated']
prefixes={'uniform':'preprints/Uniform-quasipolynomial-time-trace-reconstruction-October-5-2026/','anchor':'preprints/A-latest-anchor-induction-with-spectrally-compact-masks-for-worst-case-trace-reconstruction-October-5-2026/','lower':'preprints/quantitative-lower-bounds-for-trace-reconstruction-September-24-2026/'}
receipts=[]
for key,prefix in prefixes.items():
 for x in t['tree']:
  path=x['path']
  if x['type']!='blob' or not path.startswith(prefix) or not path.endswith(('.tex','.bib','.md')): continue
  url=f'https://raw.githubusercontent.com/openai/math/{pin}/{path}'
  data=urllib.request.urlopen(url,timeout=40).read()
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  assert len(data)==x['size'] and blob==x['sha'],path
  dest=ROOT/'private/source'/key/path[len(prefix):]; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
  receipts.append({'canonical_path':path,'url':url,'size':len(data),'git_blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'local':str(dest.relative_to(ROOT))})
(ROOT/'private/source/receipts.json').write_text(json.dumps({'pin':pin,'tree_sha256':hashlib.sha256(b).hexdigest(),'entries':13223,'blobs':receipts},indent=2))
print('authenticated',len(receipts),'pinned blobs')
