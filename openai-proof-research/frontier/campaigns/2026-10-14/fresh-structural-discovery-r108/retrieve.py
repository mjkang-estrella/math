"""Retrieve only selected pinned mathematical TeX; no shared writes."""
from pathlib import Path
import re,json,hashlib,urllib.request,concurrent.futures
ROOT=Path(__file__).resolve().parents[4]; OWN=Path(__file__).resolve().parent
REV='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); assert len(tree['tree'])==13223 and tree['truncated'] is False
cat=(ROOT/'sources/CONTENTS.md').read_text(); dirs={}
for b in re.split(r'(?=\*\*\d{3}\.)',cat)[1:]:
 n=int(b[2:5])
 if n in [104,114,124,138,184]:
  for p in re.findall(r'\]\((preprints/[^)]+\.pdf)\)',b): dirs[p.rsplit('/',1)[0]]=n
selected=[]
for e in tree['tree']:
 p=e['path']; d=next((d for d in dirs if p.startswith(d+'/')),None)
 if not d or not p.endswith('.tex') or '/tex/runtime/' in p: continue
 n=dirs[d]; name=p.rsplit('/',1)[1]
 if n!=104 and name not in {'introduction.tex','paper.tex','polyhedra.tex','counting.tex','lists.tex','checksum.tex','rounds.tex','optimizer.tex'}: continue
 selected.append((n,e))
def fetch(ne):
 n,e=ne;p=e['path'];url=f'https://raw.githubusercontent.com/openai/math/{REV}/{p}';dest=OWN/'private'/p
 rec={'family':n,'path':p,'url':url,'git_blob':e['sha']}
 try:
  b=urllib.request.urlopen(url,timeout=40).read();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==e['sha']
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  rec.update(local=str(dest.relative_to(OWN)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),git_match=True,status='retrieved',semantic_read='not yet recorded')
 except Exception as ex: rec.update(status='failed',error=str(ex))
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:r=list(pool.map(fetch,selected))
(OWN/'source-receipts.json').write_text(json.dumps(r,indent=2)+'\n');print('selected',len(r),'retrieved',sum(x['status']=='retrieved' for x in r));print([x for x in r if x['status']=='failed'])
