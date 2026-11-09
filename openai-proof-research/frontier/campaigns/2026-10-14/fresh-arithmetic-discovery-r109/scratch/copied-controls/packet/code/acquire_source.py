from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r109'
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads((P/'sources/preprints-tree.json').read_text())['tree']
items=[e for e in tree if e['type']=='blob' and ('Lex-Plus-Powers' in e['path'] or 'Division-Coefficient' in e['path']) and e['path'].endswith(('.tex','.md'))]
def get(e):
 url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path']
 with urllib.request.urlopen(url,timeout=40) as f:b=f.read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha'], e['path']
 dst=R/'private/source'/e['path'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 return {'path':e['path'],'local':str(dst.relative_to(R)),'url':url,'bytes':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: out=list(pool.map(get,items))
(R/'private/source/metadata.json').write_text(json.dumps(out,indent=2)+'\n')
print('authenticated',len(out),'source files')
