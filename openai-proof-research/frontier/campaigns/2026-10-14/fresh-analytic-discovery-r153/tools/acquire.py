from pathlib import Path
import json,urllib.request,hashlib,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153');P='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sel=json.loads((R/'private/selected-tree.json').read_text())
def get(x):
 url='https://raw.githubusercontent.com/openai/math/'+P+'/'+x['path']; p=R/'private/canonical'/x['path'];p.parent.mkdir(parents=True,exist_ok=True)
 b=urllib.request.urlopen(url,timeout=40).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==x['size'] and blob==x['sha'],x['path'];p.write_bytes(b)
 return dict(path=x['path'],local=str(p.relative_to(R)),url=url,bytes=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: out=list(pool.map(get,sel))
(R/'SOURCE-AUTH.json').write_text(json.dumps(out,indent=2)+'\n');print('Authenticated',len(out),'canonical objects;',sum(x['bytes'] for x in out),'bytes')
