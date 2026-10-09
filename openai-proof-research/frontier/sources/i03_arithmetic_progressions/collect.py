from pathlib import Path
import json, hashlib, shutil, urllib.request, concurrent.futures, subprocess
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
PIN=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
TREE={x['path']:x['sha'] for x in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']}
MAN=json.loads((ROOT/'frontier/sources/i02_arithmetic/manifest-artin.json').read_text())
records=[]
for e in MAN['files']:
    data=(ROOT/'frontier/sources/i02_arithmetic'/e['local']).read_bytes()
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob==TREE[e['path']]
    (OUT/e['local']).write_bytes(data)
    records.append(dict(path=e['path'],local=e['local'],url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{e["path"]}',git_blob=blob,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
extra='preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/references.bib'
tasks=[('pd-references.bib',f'https://raw.githubusercontent.com/openai/math/{PIN}/{extra}'),('bharadwaj-rodgers-v4.html','https://arxiv.org/html/2402.11884v4'),('ford-konyagin-luca.pdf','https://www.ford126.web.illinois.edu/wwwpapers/chains.pdf'),('moree-ap-v1.pdf','https://arxiv.org/pdf/0707.3062v1'),('goldmakher-martin-peringuey-v1.html','https://arxiv.org/html/2502.19601v1'),('murty-naik-v1.html','https://arxiv.org/html/2608.21573v1')]
def get(t):
    name,url=t
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'research-source-verification/1.0'})
        data=urllib.request.urlopen(req,timeout=45).read()
        (OUT/name).write_bytes(data)
        r=dict(local=name,url=url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
        if name=='pd-references.bib':
            blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            assert blob==TREE[extra]
            r.update(path=extra,git_blob=blob)
        if name.endswith('.pdf'):
            subprocess.run(['pdftotext','-layout',str(OUT/name),str(OUT/name.replace('.pdf','.txt'))],check=True)
        return r
    except Exception as ex:return dict(local=name,url=url,error=str(ex))
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
    external=list(pool.map(get,tasks))
inputs=[]
for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/README.md','frontier/iterations/i02-arithmetic.md','frontier/reviews/i02-arithmetic-r2.md']:
    data=(ROOT/p).read_bytes(); inputs.append(dict(path=p,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
manifest=dict(pin=PIN,upstream=records,downloads=external,inputs=inputs)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(verified_upstream=len(records),downloads=external),indent=2))
