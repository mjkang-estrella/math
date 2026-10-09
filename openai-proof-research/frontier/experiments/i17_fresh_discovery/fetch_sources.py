from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,datetime
BASE=Path(__file__).resolve().parents[3]
OUT=BASE/'frontier/sources/i17_fresh_discovery'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE=json.loads((OUT/'inputs/sources/preprints-tree.json').read_text())['tree']
KEYS=['A-classification-of-finite-Euclidean','Universal-Tensor-Squares','Cyclic-Polytabloid','Subset-Sum-in-Time','Low-Space-Algorithm-for-Worst-Case-Subset','low-temperature-Sherrington-Kirkpatrick-free-energy','low-temperature-Sherrington-Kirkpatrick-fluctuation']
entries=[e for e in TREE if e['type']=='blob' and any(k.lower() in e['path'].lower() for k in KEYS) and e['path'].endswith(('.tex','.bib','.md'))]
def get(e):
 p=e['path'];url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p
 dst=OUT/'pinned'/p;dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists(): b=dst.read_bytes()
 else:
  b=urllib.request.urlopen(url,timeout=60).read();dst.write_bytes(b)
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert sha==e['sha'],p
 return dict(path=p,local=str(dst.relative_to(BASE)),url=url,git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool: m=list(pool.map(get,entries))
(OUT/'pinned-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('Verified pinned files:',len(m))
