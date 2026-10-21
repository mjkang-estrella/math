from pathlib import Path
import urllib.request,hashlib,json,concurrent.futures
P=Path.cwd();R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r151'
assert P==Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=(P/'sources/preprints-tree.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b);assert len(t['tree'])==13223 and t['truncated']==False
prefix='preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/'
items=[x for x in t['tree'] if x['path'].startswith(prefix) and x['type']=='blob' and not x['path'].endswith('.pdf')]
def get(x):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/'+x['path']; data=urllib.request.urlopen(url,timeout=45).read()
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==x['size'] and blob==x['sha']
 q=R/'private/source'/x['path'][len(prefix):];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
 return {'canonical_path':x['path'],'url':url,'size':len(data),'git_blob_sha1':blob,'sha256':hashlib.sha256(data).hexdigest(),'local':str(q.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: receipts=list(ex.map(get,items))
(R/'private/source-authentication.json').write_text(json.dumps(receipts,indent=2)+'\n')
print('authenticated',len(receipts),'files')
