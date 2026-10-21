from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r140';pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
t=json.loads((P/'sources/preprints-tree.json').read_text())
keys=['Endpoint-convergence-for-the-planar','Endpoint-pointwise-convergence-for-the-Schrodinger']
xs=[x for x in t['tree'] if x['type']=='blob' and any(k in x['path'] for k in keys) and x['path'].endswith(('.tex','.bib','.md'))]
def get(x):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/'+x['path']; b=urllib.request.urlopen(url,timeout=45).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==x['size'] and blob==x['sha']; f=R/'private/source'/x['path'];f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b); return dict(path=x['path'],local=str(f.relative_to(R)),url=url,size=len(b),gitblob=blob,sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: out=list(pool.map(get,xs))
(R/'source-authentication.json').write_text(json.dumps({'pin':pin,'tree_sha256':hashlib.sha256((P/'sources/preprints-tree.json').read_bytes()).hexdigest(),'entries':len(t['tree']),'files':out},indent=2));print('authenticated',len(out),'files')
