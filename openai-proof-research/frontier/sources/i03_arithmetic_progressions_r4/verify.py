from pathlib import Path
import json, hashlib, urllib.request, concurrent.futures
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
SRC=ROOT/'frontier/sources/i03_arithmetic_progressions'
manifest=json.loads((SRC/'manifest.json').read_text())
pin=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
tree={e['path']:e['sha'] for e in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']}
def digest(data):
    return dict(sha256=hashlib.sha256(data).hexdigest(),git_blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),bytes=len(data))
records=[]
for rec in manifest['upstream']+manifest['downloads']:
    data=(SRC/rec['local']).read_bytes(); d=digest(data)
    assert d['sha256']==rec['sha256'],rec
    r=dict(local=rec['local'],url=rec['url'],**d)
    if 'path' in rec:
        assert d['git_blob']==tree[rec['path']]==rec['git_blob'],rec
        r.update(path=rec['path'],tree_match=True)
    records.append(r)
# Download the exact interfaces afresh, without modifying the author's cache.
need=[('The-Poisson','02-preliminaries'),('The-Poisson','05-major-arcs'),('The-Poisson','06-correlations'),('The-Poisson','07-extraction'),('The-Poisson','08-poisson-dirichlet'),('The-Poisson','09-long-prime-appendix'),('Weighted','02-transference'),('Weighted','03-ideal-kernels'),('Primitive','01a-reduction'),('Primitive','07-splitting'),('Primitive','08-type-ii'),('Simultaneous','04-marked-family')]
selected=[r for r in records if any(r['local'].startswith(pre) and r['local'].endswith('__'+tail+'.tex') for pre,tail in need)]
def fetch(r):
    url=f'https://raw.githubusercontent.com/openai/math/{pin}/{r["path"]}'
    try:
        data=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-proof-review/1.0'}),timeout=35).read()
        d=digest(data)
        assert d['sha256']==r['sha256'] and d['git_blob']==tree[r['path']]
        (OUT/r['local']).write_bytes(data)
        return dict(path=r['path'],url=url,match=True,**d)
    except Exception as e:
        return dict(path=r['path'],url=url,error=repr(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
    fresh=list(pool.map(fetch,selected))
inputs=[]
for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/README.md','frontier/findings/R004-simultaneous-bounded-index.md','frontier/reviews/i02-arithmetic-r2.md','frontier/iterations/i03-arithmetic-progressions.md','frontier/experiments/i03_arithmetic_progressions/check.py','frontier/experiments/i03_arithmetic_progressions/results.json']:
    inputs.append(dict(path=p,**digest((ROOT/p).read_bytes())))
result=dict(pin=pin,verified_cache=records,fresh_downloads=fresh,inputs=inputs)
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(cache_files=len(records),pinned_files=sum('path' in r for r in records),external_files=sum('path' not in r for r in records),fresh_downloads=len(fresh),fresh_matches=sum(r.get('match',False) for r in fresh),errors=[r for r in fresh if 'error' in r]),indent=2))
