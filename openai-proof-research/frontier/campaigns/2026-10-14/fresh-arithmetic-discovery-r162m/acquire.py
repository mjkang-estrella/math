from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162m')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
es=json.loads((ROOT/'packet/private/canonical-selection.json').read_text())
def get(e):
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
 with urllib.request.urlopen(url,timeout=45) as f: b=f.read()
 assert len(b)==e['size'],e['path']
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert git==e['sha'],e['path']
 p=ROOT/'packet/private/canonical'/e['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return dict(path=e['path'],local=str(p.relative_to(ROOT/'packet')),bytes=len(b),git_blob=git,sha256=hashlib.sha256(b).hexdigest(),url=url)
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: records=list(pool.map(get,[e for e in es if e['type']=='blob']))
(ROOT/'packet/private/canonical-authentication.json').write_text(json.dumps(records,indent=2)+'\n')
print('Authenticated',len(records),'canonical blobs',sum(e['bytes'] for e in records),'bytes')
