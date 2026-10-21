from pathlib import Path
import json,hashlib,urllib.request
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=Path.cwd()
b=(P/'sources/preprints-tree.json').read_bytes(); t=json.loads(b)
assert len(t['tree'])==13223 and not t['truncated'] and hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
(R/'private/preprints-tree.json').write_bytes(b)
records=[]
for e in t['tree']:
 if 'A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-' not in e['path'] or e['type']!='blob' or not e['path'].endswith(('.md','.tex','.bib')): continue
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 b=urllib.request.urlopen(url,timeout=40).read(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha']
 dest=R/'private/source093'/e['path'].split('/',2)[2]; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(b)
 records.append({'path':e['path'],'url':url,'size':len(b),'gitblob':blob,'sha256':hashlib.sha256(b).hexdigest(),'local':str(dest.relative_to(R))})
(R/'source-authentication.json').write_text(json.dumps(records,indent=2)); print('Authenticated',len(records),'files',sum(x['size'] for x in records),'bytes')
