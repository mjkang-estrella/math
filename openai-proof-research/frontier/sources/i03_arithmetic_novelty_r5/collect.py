"""Collect bounded novelty-review evidence; writes only beside this script."""
from pathlib import Path
import concurrent.futures, hashlib, json, subprocess, urllib.request
from html.parser import HTMLParser

class TextParser(HTMLParser):
    def __init__(self):
        super().__init__(); self.parts=[]
    def handle_data(self,data):
        if data.strip(): self.parts.append(data.strip())

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
PIN = json.loads((ROOT/'sources/upstream.json').read_text())['commit']
TREE = {x['path']: x['sha'] for x in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']}
OLD = ROOT/'frontier/sources/i03_arithmetic_progressions'
MAN = json.loads((OLD/'manifest.json').read_text())
records = []
for e in MAN['upstream'] + [e for e in MAN['downloads'] if 'git_blob' in e]:
    data = (OLD/e['local']).read_bytes()
    blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob == TREE[e['path']] == e['git_blob']
    assert hashlib.sha256(data).hexdigest() == e['sha256']
    (OUT/e['local']).write_bytes(data)
    records.append(dict(e, provenance='inherited bytes independently checked against pinned tree'))

extra = [
 'preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex',
 'preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex',
 'preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/sections/introduction.tex',
 'preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/introduction.tex',
 'preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/build/sections/00-introduction.tex',
 'preprints/Deterministic-Polynomial-Factorization-over-Prime-Fields-October-4-2026/build/sections/10-analytic.tex',
]
tasks = [(p.replace('preprints/','').replace('/','__'), f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}',p) for p in extra]
tasks += [
 ('carella-v14.html','https://arxiv.org/html/1707.06517v14',None),
 ('carella-v14-abstract.html','https://arxiv.org/abs/1707.06517v14',None),
 ('pollack-2025-v1.html','https://arxiv.org/html/2505.05601v1',None),
 ('bharadwaj-rodgers-published.pdf','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/270043D7BAB4CDA2A601A061FB482AA0/S0008439526101982a.pdf/large_prime_factors_of_welldistributed_sequences.pdf',None),
]
def download(t):
    name,url,path=t
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'research-review/1.0'})
        if (OUT/name).exists():
            data=(OUT/name).read_bytes(); final=url
        else:
            with urllib.request.urlopen(req,timeout=40) as f: data=f.read(); final=f.url
        (OUT/name).write_bytes(data)
        r=dict(local=name,url=url,final_url=final,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        if path:
            blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            assert blob == TREE[path]
            r.update(path=path,git_blob=blob)
        if name.endswith('.pdf'):
            subprocess.run(['pdftotext','-layout',str(OUT/name),str(OUT/(name[:-4]+'.txt'))],check=True)
        if name.endswith('.html'):
            parser=TextParser(); parser.feed(data.decode('utf-8'))
            (OUT/(name[:-5]+'.txt')).write_text('\n'.join(parser.parts))
        return r
    except Exception as e:
        return dict(local=name,url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
    downloads=list(pool.map(download,tasks))
for e in MAN['downloads']:
    if 'git_blob' in e: continue
    data=(OLD/e['local']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==e['sha256']
    (OUT/e['local']).write_bytes(data)
    downloads.append(dict(e,provenance='prior primary retrieval, hash rechecked'))
    p=OLD/Path(e['local']).with_suffix('.txt')
    if p.exists(): (OUT/p.name).write_bytes(p.read_bytes())

inputs=[]
for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/README.md','frontier/iterations/README.md','frontier/iterations/i03-arithmetic-progressions.md','frontier/reviews/i03-arithmetic-progressions-r4.md','frontier/sources/i03_arithmetic_progressions/parent-preliminary-review.md','frontier/reviews/i02-arithmetic-r2.md']:
    b=(ROOT/p).read_bytes()
    inputs.append(dict(path=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
result=dict(pin=PIN,date='2026-10-08',upstream=records,downloads=downloads,inputs=inputs)
(OUT/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(verified_inherited=len(records),fresh_downloads=downloads[:len(tasks)]),indent=2))
