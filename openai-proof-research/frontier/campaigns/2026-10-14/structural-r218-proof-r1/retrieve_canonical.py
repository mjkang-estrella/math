import concurrent.futures,hashlib,json,urllib.request,os
from pathlib import Path
os.umask(0o077)
r=Path(__file__).resolve().parent; a=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r218');pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=Path('sources/preprints-tree.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tr=json.loads(b)['tree']
families=['Taming-implies-compatibility-on-four-manifolds-October-6-2026','Taming-implies-compatibility-on-four-manifolds-September-23-2026']
selected=[x for x in tr if x['type']=='blob' and any(x['path'].startswith(f+'/') or x['path'].startswith('preprints/'+f+'/') for f in families)]
assert len(selected)==25,len(selected)
def get(x):
 path=x['path'];path=path if path.startswith('preprints/') else 'preprints/'+path
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/{path}'
 with urllib.request.urlopen(url,timeout=40) as h:b=h.read()
 assert len(b)==x['size'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['sha']
 assert b==(a/'private/canonical'/path).read_bytes()
 p=r/'private/retrieved'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':path,'url':url,'bytes':len(b),'blob_sha1':x['sha'],'sha256':hashlib.sha256(b).hexdigest(),'equal_to_admitted_author':True}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:out=list(pool.map(get,selected))
(r/'private/retrieved-canonical.json').write_text(json.dumps(out,indent=2)+'\n')
print('Independently retrieved and authenticated',len(out),'Source342 blobs against complete pinned tree and exact admitted bytes.')
g=json.loads((r/'private/guards.json').read_bytes());ag=json.loads((a/'private/guards.json').read_bytes());g['derivative_patterns']=ag['derivative_wildcards'];(r/'private/guards.json').write_text(json.dumps(g,indent=2)+'\n')
print('All supplemental derivative guards installed with full-path leading wildcards.')
