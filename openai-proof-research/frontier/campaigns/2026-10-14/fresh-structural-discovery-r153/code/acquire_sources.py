import json,hashlib,urllib.request,concurrent.futures
from pathlib import Path
ROOT=Path.cwd();assert str(ROOT)=='/home/mj-kang/Documents/Dev/math/openai-proof-research'
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r153'
b=(ROOT/'sources/preprints-tree.json').read_bytes();assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b);assert len(t['tree'])==13223 and not t['truncated']
prefixes=['An-exponential-state-lower-bound-for-two-way-nondeterministic-complementation-September-25-2026','An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026']
entries=[e for e in t['tree'] if e['type']=='blob' and any(e['path'].startswith('preprints/'+p+'/') for p in prefixes) and not e['path'].endswith('.pdf')]
def get(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 data=urllib.request.urlopen(url,timeout=40).read();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==e['size'] and blob==e['sha']
 local=OUT/'private/sources'/e['path'];local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(data)
 return {'canonical':e['path'],'url':url,'bytes':len(data),'git_blob_sha1':blob,'sha256':hashlib.sha256(data).hexdigest(),'copy':str(local.relative_to(OUT))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: records=list(pool.map(get,entries))
(OUT/'private/sources/authentication.json').write_text(json.dumps(records,indent=2)+'\n')
print('Authenticated',len(records),'non-PDF canonical source files')
