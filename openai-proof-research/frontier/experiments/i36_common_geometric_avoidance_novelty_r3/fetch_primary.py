"""Fresh bounded primary retrieval; writes only this review's literature directory."""
from pathlib import Path
import concurrent.futures,datetime,hashlib,json,urllib.request
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i36_common_geometric_avoidance_novelty_r3/literature'
urls={
'jiang-current':'https://arxiv.org/abs/2610.11449',
'burgin-current':'https://arxiv.org/abs/2210.09284',
'chlebik-current':'https://arxiv.org/abs/1512.05607',
'kp-current':'https://arxiv.org/abs/2208.02637',
'survey-current':'https://arxiv.org/abs/2412.11062',
'withdrawn-current':'https://arxiv.org/abs/2001.02395',
'jiang-v1':'https://arxiv.org/pdf/2610.11449v1',
'burgin-v1':'https://arxiv.org/pdf/2210.09284v1',
'chlebik-v1':'https://arxiv.org/pdf/1512.05607v1',
'kp-published':'https://msp.org/apde/2025/18-1/apde-v18-n1-p02-p.pdf',
'kolountzakis-1997':'https://eigen-space.org/mk/ps/universal.pdf',
}
def fetch(pair):
 name,url=pair;r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research review provenance'}),timeout=45) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  dst=S/(name+('.pdf' if b.startswith(b'%PDF') else '.html'));dst.write_bytes(b)
  r.update(path=str(dst.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['failure']=repr(e)
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool: rows=list(pool.map(fetch,urls.items()))
(S/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ('name','status','failure','bytes') if k in r} for r in rows],indent=2))
