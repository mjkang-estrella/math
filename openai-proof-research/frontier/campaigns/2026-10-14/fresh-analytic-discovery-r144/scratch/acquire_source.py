from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
root=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r144')
folder='preprints/De-Giorgis-conjecture-in-dimension-eight-September-26-2026/'
tree=json.loads(Path('sources/preprints-tree.json').read_bytes())
entries=[e for e in tree['tree'] if e['path'].startswith(folder) and e['type']=='blob' and not e['path'].endswith('.pdf')]
def get(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 b=urllib.request.urlopen(url,timeout=45).read(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha']
 p=root/'private/source'/e['path'][len(folder):]; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
 return {'canonical_path':e['path'],'url':url,'size':len(b),'git_blob_sha1':blob,'sha256':hashlib.sha256(b).hexdigest(),'local':str(p.relative_to(root))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: rows=list(pool.map(get,entries))
(root/'SOURCE-AUTH.json').write_text(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','tree_entries':13223,'files':rows},indent=2)+'\n')
print('authenticated',len(rows),'files',sum(r['size'] for r in rows),'bytes')
