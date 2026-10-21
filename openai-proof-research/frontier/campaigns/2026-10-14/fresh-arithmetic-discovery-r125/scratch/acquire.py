from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r125')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads(Path('sources/preprints-tree.json').read_bytes())['tree']
prefix='preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/'
sel=[x for x in tree if x['type']=='blob' and x['path'].startswith(prefix) and x['path'].endswith('.tex')]
def get(x):
 url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{x["path"]}'
 with urllib.request.urlopen(url,timeout=45) as r:b=r.read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert blob==x['sha'] and len(b)==x['size']
 out=R/'private/source'/Path(x['path']).name;out.write_bytes(b)
 return dict(canonical=x['path'],url=url,size=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),copy=str(out.relative_to(R)))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rec=list(ex.map(get,sel))
(R/'private/source-identities.json').write_text(json.dumps(rec,indent=2)+'\n')
print('authenticated',len(rec),'canonical TeX blobs')
