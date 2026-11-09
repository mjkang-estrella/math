from pathlib import Path
import json,hashlib,urllib.request
ROOT=Path.cwd(); out=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r114/packet/private/source'
tree=json.loads((ROOT/'sources/preprints-tree.json').read_bytes())
prefix='preprints/Integral-points-on-character-varieties-of-curves-September-25-2026/'
commit='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'; records=[]
for e in tree['tree']:
 if e['path'].startswith(prefix) and e['type']=='blob' and e['path'].endswith(('.md','.tex','.bib')):
  url=f'https://raw.githubusercontent.com/openai/math/{commit}/{e["path"]}'
  b=urllib.request.urlopen(url,timeout=40).read()
  blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==e['size'] and blob==e['sha']
  rel=e['path'][len(prefix):]; p=out/rel; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
  records.append(dict(path=e['path'],local=rel,url=url,size=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest()))
(out/'authentication.json').write_text(json.dumps(records,indent=2)+'\n')
print('authenticated',len(records),'source text blobs')
