from pathlib import Path
import json,urllib.request,hashlib,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r133')
T=json.loads((R/'private/source/tree-selected.json').read_text())
P='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def get(e):
 p=e['path']; url=f'https://raw.githubusercontent.com/openai/math/{P}/{p}'
 b=urllib.request.urlopen(url,timeout=40).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert sha==e['sha'] and len(b)==e['size'],p
 name=('two-sided' if '/A-negatively-' in p else 'one-sided')+'/'+p.split('/build/')[1]
 dst=R/'private/source'/name; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b)
 return dict(path=p,url=url,size=len(b),gitblob=sha,sha256=hashlib.sha256(b).hexdigest(),local=str(dst.relative_to(R)))
sel=[e for e in T if e['type']=='blob' and '/build/' in e['path'] and '/figures/' not in e['path']]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: records=list(ex.map(get,sel))
(R/'private/source/authentication.json').write_text(json.dumps(records,indent=2)+'\n')
print('Authenticated',len(records),'canonical source and bibliography objects.')
for side in ['two-sided','one-sided']:
 print((R/f'private/source/{side}/main.tex').read_text())
