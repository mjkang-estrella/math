from pathlib import Path
import json,urllib.request,hashlib
ROOT=Path.cwd(); out=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r121/packet/private/source';out.mkdir(exist_ok=True)
T=json.loads((ROOT/'sources/preprints-tree.json').read_bytes())['tree'];pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
prefixes=['preprints/The-p-adic-section-conjecture-October-6-2026/build/','preprints/Etale-covers-with-a-prescribed-exterior-sheet-September-24-2026/build/']
records=[]
for e in T:
 if e['type']!='blob' or not e['path'].endswith(('.tex','.bib')) or not any(e['path'].startswith(p) for p in prefixes):continue
 url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path']
 b=urllib.request.urlopen(url,timeout=40).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha']
 tag='section-' if '/The-p-adic-' in e['path'] else 'exterior-'
 dest=out/(tag+Path(e['path']).name);dest.write_bytes(b)
 records.append({'canonical_path':e['path'],'url':url,'size':len(b),'git_blob_sha1':blob,'sha256':hashlib.sha256(b).hexdigest(),'copy':str(dest.relative_to(ROOT))})
(out.parent/'source-identities.json').write_text(json.dumps(records,indent=2));print('authenticated',len(records),'pinned blobs')
