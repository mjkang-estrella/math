"""Bounded supplemental primary retrieval; immutable first capture."""
from pathlib import Path
import concurrent.futures,urllib.request,datetime,hashlib,json,subprocess
R=Path(__file__).resolve().parents[3];D=R/'frontier/sources/i64_entropy_coefficient_extraction_novelty/literature'
requests=[('hosvd','https://www.math.ucdavis.edu/~saito/data/tensor/lathauwer-etal_mulilinear-SVD.pdf'),('yang-hodge','https://arxiv.org/pdf/1111.1295'),('korn','https://arxiv.org/pdf/1302.2661')]
def fetch(pair):
 n,u=pair;r=dict(name=n,url=u,time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(u,timeout=30) as f:b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  p=D/(n+'.pdf');p.write_bytes(b);assert b.startswith(b'%PDF')
  t=subprocess.check_output(['pdftotext','-layout',str(p),'-']);q=D/(n+'.txt');q.write_bytes(t)
  r.update(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),text_path=str(q.relative_to(R)),text_sha256=hashlib.sha256(t).hexdigest())
 except Exception as e:r['error']=repr(e)
 return r
assert not (D/'supplement.json').exists()
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:a=list(ex.map(fetch,requests))
(D/'supplement.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps([{k:v for k,v in x.items() if k in ('name','status','error')} for x in a]))
