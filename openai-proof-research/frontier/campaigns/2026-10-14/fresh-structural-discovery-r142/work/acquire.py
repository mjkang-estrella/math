from pathlib import Path
import urllib.request,hashlib,json,concurrent.futures
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r142'
t=json.loads((P/'sources/preprints-tree.json').read_text())['tree'];pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
rows=[x for x in t if x['type']=='blob' and ('The-Artinian-Lex-Plus-Powers-' in x['path'] or 'Commuting-Division-Coefficient-' in x['path']) and x['path'].endswith(('.tex','README.md'))]
def get(x):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/{x["path"]}'
 with urllib.request.urlopen(url,timeout=40) as f:b=f.read()
 h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert h==x['sha'],(x['path'],h)
 out=R/'packet/private/upstream'/x['path'];out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
 return {'path':x['path'],'url':url,'git_blob':h,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: records=list(pool.map(get,rows))
(R/'packet/private/upstream-acquisition.json').write_text(json.dumps(records,indent=2));print('authenticated',len(records),'blobs')
