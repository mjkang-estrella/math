from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r111/packet'; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
t=json.loads((P/'sources/preprints-tree.json').read_text())['tree']
sel=[x for x in t if x['type']=='blob' and ('/Donovans-Conjecture-' in '/'+x['path'] or '/Integral-Donovan-Finiteness-' in '/'+x['path']) and x['path'].endswith(('.tex','.bib','.md'))]
def get(x):
 u=f'https://raw.githubusercontent.com/openai/math/{pin}/{x["path"]}';b=urllib.request.urlopen(u,timeout=45).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==x['size'] and blob==x['sha'];f=R/'private/source'/x['path'];f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);return {'path':x['path'],'url':u,'size':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e:out=list(e.map(get,sel))
(R/'private/source/metadata.json').write_text(json.dumps(out,indent=2)+'\n');print('Authenticated',len(out),'source files')
