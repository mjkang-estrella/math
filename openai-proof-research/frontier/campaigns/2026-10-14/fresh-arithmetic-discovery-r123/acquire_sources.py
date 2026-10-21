from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r123'); T=json.loads(Path('sources/preprints-tree.json').read_bytes())['tree']; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
selected=[e for e in T if e['type']=='blob' and 'The-Margulis-Platonov-conjecture-over-' in e['path'] and e['path'].endswith(('.tex','.bib')) and 'figures/' not in e['path']]
def get(e):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/{e["path"]}'
 b=urllib.request.urlopen(url,timeout=40).read(); git=hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()
 assert len(b)==e['size'] and git==e['sha'],e['path']
 q=R/'private/pinned'/e['path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 return {'canonical_path':e['path'],'url':url,'size':len(b),'git_blob':git,'sha256':hashlib.sha256(b).hexdigest(),'selected_copy':str(q.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:rows=list(ex.map(get,selected))
(R/'private/source-identities.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Authenticated',len(rows),'canonical blobs')
