from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
P=Path.cwd(); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r115'; T=json.loads((P/'sources/preprints-tree.json').read_text())
D=['The-p-adic-section-conjecture-October-6-2026','Etale-covers-with-a-prescribed-exterior-sheet-September-24-2026']
entries=[x for x in T['tree'] if x['type']=='blob' and any(x['path'].startswith('preprints/'+d+'/') for d in D) and not x['path'].endswith('.pdf')]
def get(x):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']; b=urllib.request.urlopen(url,timeout=40).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==x['size'] and sha==x['sha'],x['path']
 p=R/'packet/private/source'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return dict(path=x['path'],size=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),url=url,copy=str(p.relative_to(R)))
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex: rows=list(ex.map(get,entries))
(R/'packet/source-identities.json').write_text(json.dumps(rows,indent=2)+'\n')
for x in rows:print(x['path'],x['size'])
