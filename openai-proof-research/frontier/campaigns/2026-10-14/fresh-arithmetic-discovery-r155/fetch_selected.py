from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,time
p=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r155/packet/private')
rows=json.loads((p/'selected-tree.json').read_text())
def fetch(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 out=p/'upstream'/e['path']; out.parent.mkdir(parents=True,exist_ok=True)
 for attempt in range(3):
  try:
   b=urllib.request.urlopen(url,timeout=45).read(); sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
   assert len(b)==e['size'] and sha==e['sha'], (e['path'],len(b),sha)
   out.write_bytes(b)
   return dict(path=e['path'],url=url,size=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),authenticated=True)
  except Exception as ex:
   if attempt==2: return dict(path=e['path'],error=str(ex))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool: results=list(pool.map(fetch,rows))
(p/'authentication.json').write_text(json.dumps(results,indent=2)+'\n')
print('Authenticated',sum(r.get('authenticated',False) for r in results),'of',len(rows)); print([r for r in results if 'error' in r])
