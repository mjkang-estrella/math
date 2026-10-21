from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r154')
t=json.loads(Path('sources/preprints-tree.json').read_text())
prefixes=['preprints/An-FPRAS-for-Common-Integer-Polymatroid-Bases-with-Binary-Capacities-October-5-2026/','preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/']
entries=[e for e in t['tree'] if e['type']=='blob' and e['path'].startswith(tuple(prefixes)) and not e['path'].endswith('.pdf')]
def get(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 b=urllib.request.urlopen(url,timeout=45).read(); h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and h==e['sha']
 p=R/'private/sources'/e['path']; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
 return dict(canonical_path=e['path'],url=url,size=len(b),gitblob=h,sha256=hashlib.sha256(b).hexdigest(),local=str(p.relative_to(R)))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: out=list(pool.map(get,entries))
(R/'private/source-identities.json').write_text(json.dumps(out,indent=2)+'\n')
print('authenticated',len(out),'canonical source files')
