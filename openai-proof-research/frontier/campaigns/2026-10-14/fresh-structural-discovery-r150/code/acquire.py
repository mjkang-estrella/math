from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r150'
b=(P/'sources/preprints-tree.json').read_bytes(); assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
d=json.loads(b); assert len(d['tree'])==13223 and d['truncated']==False
pref='preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/'
entries=[e for e in d['tree'] if e['path'].startswith(pref) and e['type']=='blob']
def get(e):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 data=urllib.request.urlopen(url,timeout=45).read(); blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==e['size'] and blob==e['sha']
 path=R/'private/source131'/e['path'][len(pref):];path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
 return dict(canonical_path=e['path'],size=len(data),git_blob=blob,sha256=hashlib.sha256(data).hexdigest(),url=url,local=str(path.relative_to(R)))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: receipts=list(ex.map(get,entries))
(R/'private/source-authentication.json').write_text(json.dumps({'tree_sha256':hashlib.sha256(b).hexdigest(),'entries':len(d['tree']),'files':receipts},indent=2))
print('authenticated',len(receipts))
