from pathlib import Path
import urllib.request,hashlib,json,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r158'); pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
rows=json.loads((R/'private/tree-selection.json').read_text())['selected']
selected=[x for x in rows if x['type']=='blob' and (x['path'].endswith(('.tex','.bib')) or x['path'].endswith('/README.md')) and '/verification/' not in x['path']]
def get(x):
 path=x['path']; url=f'https://raw.githubusercontent.com/openai/math/{pin}/{path}'; b=urllib.request.urlopen(url,timeout=45).read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert len(b)==x['size'] and blob==x['sha']
 target=R/'private/source'/path; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(b)
 return {'canonical_path':path,'url':url,'size':len(b),'git_blob_sha1':blob,'sha256':hashlib.sha256(b).hexdigest(),'selected_copy':str(target.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: out=list(pool.map(get,selected))
(R/'private/source-identities.json').write_text(json.dumps(out,indent=2)); print('Authenticated',len(out),'text objects;',sum(x['size'] for x in out),'bytes')
