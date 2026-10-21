from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r117'); pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sel=json.loads((R/'packet/tree-selection.json').read_text())['selected']
sel=[x for x in sel if x['type']=='blob' and not x['path'].endswith('.pdf')]
def get(pair):
 i,x=pair;url=f'https://raw.githubusercontent.com/openai/math/{pin}/{x["path"]}'
 b=urllib.request.urlopen(url,timeout=45).read();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert git==x['sha'] and len(b)==x['size'],x['path']
 name=f'{i:02d}-'+x['path'].split('/')[-1];dest=R/'packet/private/source'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 return {'canonical_path':x['path'],'url':url,'size':len(b),'gitblob':git,'sha256':hashlib.sha256(b).hexdigest(),'selected_copy':str(dest.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: ids=list(pool.map(get,enumerate(sel,1)))
(R/'packet/source-identities.json').write_text(json.dumps(ids,indent=2));print(json.dumps([{'copy':x['selected_copy'],'size':x['size']} for x in ids],indent=2))
