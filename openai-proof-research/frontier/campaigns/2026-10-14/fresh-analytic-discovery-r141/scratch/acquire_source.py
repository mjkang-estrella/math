from pathlib import Path
import json,hashlib,urllib.request,re,concurrent.futures
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r141'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
c=(ROOT/'sources/CONTENTS.md').read_text(); sec=c[c.index('**376.'):];sec=sec.split('**377.')[0]
names=set(re.findall(r'\]\((preprints/[^/]+)/[^)]+\)',sec))
print('COMPANIONS',len(names));print('\n'.join(sorted(names)))
treebytes=(ROOT/'sources/preprints-tree.json').read_bytes();j=json.loads(treebytes)
assert len(j['tree'])==13223 and not j['truncated'] and hashlib.sha256(treebytes).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
rows=[x for x in j['tree'] if x['type']=='blob' and '/'.join(x['path'].split('/')[:2]) in names and x['path'].endswith(('.tex','.bib','.md'))]
def get(x):
 u=f'https://raw.githubusercontent.com/openai/math/{PIN}/{x["path"]}'
 b=urllib.request.urlopen(u,timeout=40).read();sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert sha==x['sha'] and len(b)==x['size'],x['path']
 q=OUT/'private/source'/x['path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 return dict(path=x['path'],url=u,size=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),local=str(q.relative_to(OUT)))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:res=list(ex.map(get,rows))
(OUT/'source-authentication.json').write_text(json.dumps({'pin':PIN,'canonical_tree_sha256':hashlib.sha256(treebytes).hexdigest(),'canonical_tree_entries':13223,'files':res},indent=2)+'\n')
print('Authenticated',len(res),'blobs',sum(x['size'] for x in res),'bytes')
for x in res:print(x['path'],x['size'])
