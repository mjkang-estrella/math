import json,hashlib,urllib.request,datetime
from pathlib import Path
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r105'; D=R/'packet/private'
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=(P/'sources/preprints-tree.json').read_bytes(); assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
(D/'context/preprints-tree.json').write_bytes(b)
receipts=[]
for e in json.loads(b)['tree']:
 path=e['path']
 if 'An-algebra-of-infinite-little-finitistic-dimension-' not in path or not path.endswith(('.tex','.bib','.md')):continue
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/{path}'
 data=urllib.request.urlopen(url,timeout=45).read()
 sha=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==e['size'] and sha==e['sha']
 dest=D/'sources'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 receipts.append(dict(path=path,url=url,size=len(data),git_blob_sha1=sha,sha256=hashlib.sha256(data).hexdigest(),acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),read=False))
(D/'sources/acquisition.json').write_text(json.dumps(receipts,indent=2)+'\n')
print('acquired',len(receipts),'authenticated pinned text files')
