# Original code, MIT; bounded acquisition, immutable pin, local writes only.
from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r152')
assert Path.cwd()==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=Path('sources/preprints-tree.json').read_bytes(); assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(b);assert len(tree['tree'])==13223 and not tree['truncated']
prefixes={'balanced':'preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/','extension':'preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/'}
jobs=[(kind,prefix,e) for kind,prefix in prefixes.items() for e in tree['tree'] if e['path'].startswith(prefix) and e['type']=='blob' and not e['path'].endswith('.pdf')]
def fetch(job):
 kind,prefix,e=job;url=f"https://raw.githubusercontent.com/openai/math/{PIN}/{e['path']}"
 data=urllib.request.urlopen(url,timeout=45).read()
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==e['size'] and blob==e['sha'],e['path']
 p=ROOT/'private/source'/kind/e['path'][len(prefix):];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 return {'canonical_path':e['path'],'url':url,'size':len(data),'git_blob_sha1':blob,'sha256':hashlib.sha256(data).hexdigest(),'local_path':str(p.relative_to(ROOT))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: rows=list(ex.map(fetch,jobs))
(ROOT/'private/source-authentication.json').write_text(json.dumps({'pin':PIN,'tree_sha256':hashlib.sha256(b).hexdigest(),'tree_entries':13223,'files':rows},indent=2)+'\n')
print('Authenticated',len(rows),'non-PDF source files')
