from pathlib import Path
import json,hashlib,urllib.request
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r150'); dest=r/'private/pinned-source'; dest.mkdir(exist_ok=True)
rows=[]
for e in json.loads((r/'private/source-tree-selection.json').read_text()):
 if not e['path'].endswith(('.tex','.bib')): continue
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']; b=urllib.request.urlopen(url,timeout=45).read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert blob==e['sha'] and len(b)==e['size']
 path=dest/Path(e['path']).name; path.write_bytes(b)
 rows.append({'canonical_path':e['path'],'url':url,'size':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'selected_copy':str(path.relative_to(r))})
(r/'SOURCE-AUTH.json').write_text(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','objects':rows},indent=2)+'\n')
print('Authenticated',len(rows),'objects',sum(x['size'] for x in rows),'bytes')
