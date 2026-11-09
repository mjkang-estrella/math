from pathlib import Path
import hashlib,json,urllib.request,sys
ROOT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
BASE=ROOT/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r82'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); entries={e['path']:e for e in tree['tree']}
pp=BASE/'packet/private/source-provenance.json'
records=json.loads(pp.read_text()) if pp.exists() else []
for p in sys.argv[1:]:
 e=entries[p]; dest=BASE/'packet/private/upstream'/p
 if dest.exists(): continue
 url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'
 data=urllib.request.urlopen(url,timeout=60).read()
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert blob==e['sha'],p
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
 records.append({'path':str(dest.relative_to(BASE/'packet')),'upstream_path':p,'url':url,'git_blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'size':len(data)})
 print(len(data),p)
pp.write_text(json.dumps(records,indent=2)+'\n')
(BASE/'packet/private/canonical-selection.json').write_text(json.dumps({'pin':PIN,'tree_sha256':hashlib.sha256((ROOT/'sources/preprints-tree.json').read_bytes()).hexdigest(),'entry_count':len(entries),'truncated':tree['truncated'],'entries':[entries[r['upstream_path']] for r in records]},indent=2)+'\n')
