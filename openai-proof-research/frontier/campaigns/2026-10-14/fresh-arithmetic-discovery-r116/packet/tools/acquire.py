from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r116');D=R/'packet/private/sources';D.mkdir(exist_ok=True)
entries=[e for e in json.loads((R/'packet/private/tree-selection.json').read_text()) if e['type']=='blob' and not e['path'].endswith('.pdf')]
commit='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def get(z):
 i,e=z;url='https://raw.githubusercontent.com/openai/math/'+commit+'/'+e['path'];b=urllib.request.urlopen(url,timeout=40).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==e['size'] and blob==e['sha'];name=f'{i:02d}-'+Path(e['path']).name;(D/name).write_bytes(b);return dict(e,local=str((D/name).relative_to(R)),url=url,sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:out=list(ex.map(get,enumerate(entries,1)))
(R/'packet/source-identities.json').write_text(json.dumps(out,indent=2))
for e in out:print(Path(e['local']).name,e['size'])
