import json,hashlib,re,sys
from pathlib import Path
R=Path(sys.argv[1]);D=R.parent/'expanded-corpus-r178';tree=json.loads((R/'downloads/pool-tree/body').read_text());assert not tree['truncated']
rows=[]
for x in tree['tree']:
 p=x['path']
 if x['type']=='blob' and p.startswith('candidates/'):
  cached=D/'sources'/('pool-'+p.replace('/','__'))
  if not cached.exists():rows.append({'path':p,'missing':True});continue
  b=cached.read_bytes();h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert h==x['sha'],p
  hits=[(i,l) for i,l in enumerate(b.decode().splitlines(),1) if re.search(r'360905|orientable.*dominat|Hansen|forced.head',l,re.I)]
  rows.append({'path':p,'git_blob_sha':h,'sha256':hashlib.sha256(b).hexdigest(),'live_tree_matches_cached_bytes':True,'hits':hits})
(R/'registry.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
