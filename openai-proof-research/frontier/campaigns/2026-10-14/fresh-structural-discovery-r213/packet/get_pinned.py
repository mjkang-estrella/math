from pathlib import Path
import hashlib,json,urllib.request,concurrent.futures,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r213')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sel=json.loads((R/'private/tree-selection.json').read_text())
blobs=[x for x in sel if x['type']=='blob']
assert len(blobs)==32

def get(x):
 url=f'https://raw.githubusercontent.com/openai/math/{PIN}/'+x['path']
 b=urllib.request.urlopen(url,timeout=45).read()
 g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==x['size'] and g==x['sha'],x['path']
 p=R/'private/pinned'/x['path']; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
 return {'path':x['path'],'bytes':len(b),'git_blob_sha1':g,'sha256':hashlib.sha256(b).hexdigest(),'url':url,'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 out=list(pool.map(get,blobs))
(R/'private/authenticated.json').write_text(json.dumps(out,indent=2)+'\n')
url=f'https://raw.githubusercontent.com/openai/math/{PIN}/lean/docs/337.md'
b=urllib.request.urlopen(url,timeout=45).read()
(R/'private/lean-337.md').write_bytes(b)
print('Authenticated',len(out),'canonical blobs; total bytes',sum(x['bytes'] for x in out))
print('--- Lean navigation ---')
print(b.decode())
