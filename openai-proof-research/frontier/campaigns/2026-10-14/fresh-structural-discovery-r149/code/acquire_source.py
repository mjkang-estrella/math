from pathlib import Path
import json,hashlib,urllib.request
ROOT=Path(__file__).resolve().parents[1]
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=(PROJECT/'sources/preprints-tree.json').read_bytes();j=json.loads(b)
assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
assert len(j['tree'])==13223 and not j['truncated']
(ROOT/'private/tree-authentication.json').write_text(json.dumps({'path':'sources/preprints-tree.json','bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'entries':len(j['tree']),'truncated':j['truncated']},indent=2))
receipts=[]
for e in j['tree']:
 p=e['path']
 if not any(p.startswith('preprints/'+x) for x in ['The-strong-thin-tree-conjecture-September-23-2026/','A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/']):continue
 if e['type']!='blob' or not p.endswith(('.tex','.bib','.md')):continue
 url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'
 data=urllib.request.urlopen(url,timeout=40).read()
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==e['size'] and blob==e['sha'],p
 dest=ROOT/'private/source'/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 receipts.append({'path':p,'url':url,'bytes':len(data),'git_blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'local':str(dest.relative_to(ROOT))})
(ROOT/'private/source-receipts.json').write_text(json.dumps(receipts,indent=2));print('authenticated',len(receipts),'source files')
