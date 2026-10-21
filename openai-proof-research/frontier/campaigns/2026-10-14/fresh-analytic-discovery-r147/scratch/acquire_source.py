from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147');pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sel=json.loads((R/'private/source/tree-selection.json').read_text())
def get(e):
 path=e['path'];url=f'https://raw.githubusercontent.com/openai/math/{pin}/{path}'
 b=urllib.request.urlopen(url,timeout=40).read();sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and sha==e['sha'],path
 tag='global' if '/Global-' in path else 'holder';dest=R/'private/source'/tag/Path(path).relative_to(Path(*Path(path).parts[:2]));dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 return {'canonical_path':path,'url':url,'size':len(b),'git_blob_sha1':sha,'sha256':hashlib.sha256(b).hexdigest(),'copy':str(dest.relative_to(R))}
entries=[e for e in sel if e['type']=='blob' and not e['path'].endswith('.pdf')]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:records=list(ex.map(get,entries))
(R/'SOURCE-AUTH.json').write_text(json.dumps({'pin':pin,'tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','entry_count':13223,'files':records},indent=2)+'\n')
print('authenticated',len(records),'source bodies')
