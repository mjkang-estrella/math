from pathlib import Path
import json,hashlib,urllib.request
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT.parents[3]
TREE=json.loads((PROJECT/'sources/preprints-tree.json').read_bytes())['tree']
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
records=[]
for e in TREE:
 if 'Short-Egyptian-fractions-September-25-2026/build/' not in e['path'] or not e['path'].endswith(('.tex','.bib')): continue
 url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{e["path"]}'
 dst=ROOT/'private/upstream'/e['path'];dst.parent.mkdir(parents=True,exist_ok=True)
 b=urllib.request.urlopen(url,timeout=45).read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha'],e['path']
 dst.write_bytes(b)
 records.append(dict(path=e['path'],url=url,size=len(b),gitblob=blob,sha256=hashlib.sha256(b).hexdigest(),local=str(dst.relative_to(ROOT))))
(ROOT/'private/source-metadata.json').write_text(json.dumps(records,indent=2)+'\n')
print('authenticated',len(records),'source files')
