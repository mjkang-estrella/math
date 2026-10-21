from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,fnmatch
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r149')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads(Path('sources/preprints-tree.json').read_text())['tree']
blocked=json.loads((ROOT/'private/exclusions.json').read_text())['active_and_recent_literal_globs']
entries=[e for e in tree if not any(fnmatch.fnmatchcase(e['path'].lower(),g) for g in blocked) and 'lieb-thirring' in e['path'].lower() and e['path'].endswith(('.tex','.bib'))]
def get(e):
 p=e['path']; url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'
 with urllib.request.urlopen(url,timeout=45) as r:b=r.read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if len(b)!=e['size'] or blob!=e['sha']:raise ValueError(p)
 name=p.split('/')[1]+'/'+p.split('/build/')[1]; local=ROOT/'private/source'/name
 local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(b)
 return {'canonical_path':p,'pinned_url':url,'tree_size':e['size'],'git_blob_sha1':blob,'sha256':hashlib.sha256(b).hexdigest(),'selected_path':str(local.relative_to(ROOT)),'semantic_read':'acquired; extents separately recorded'}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:records=list(ex.map(get,entries))
(ROOT/'SOURCE-AUTH.json').write_text(json.dumps(records,indent=2)+'\n')
print('Authenticated',len(records),'source files',sum(r['tree_size'] for r in records),'bytes')
