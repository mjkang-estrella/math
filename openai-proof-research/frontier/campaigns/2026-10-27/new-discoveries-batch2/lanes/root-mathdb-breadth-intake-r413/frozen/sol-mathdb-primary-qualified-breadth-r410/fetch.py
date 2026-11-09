from pathlib import Path
import urllib.request,urllib.error,json,datetime,hashlib,concurrent.futures
L=Path(__file__).parent;P=L/'primary';P.mkdir(exist_ok=True)
urls={'erickson':'https://jeffe.cs.illinois.edu/open/algo.html','eppstein':'https://ics.uci.edu/~eppstein/junkyard/open.html','ollivier':'https://www.yann-ollivier.org/rech/publs/problems_curvmarkov.pdf','boyle':'https://www.math.umd.edu/~mboyle/papers/openfinalsub3nov2007.pdf','gasull':'https://arxiv.org/pdf/2012.02524v1','ergodic':'https://arxiv.org/pdf/1103.3808v1','stonybrook':'https://www.math.stonybrook.edu/open-problems-dynamical-systems','chern':'https://people.math.harvard.edu/~hirolee/pdfs/2014-fall-230a-icm1970-chern-differential-geometry.pdf','soap':'http://torus.math.uiuc.edu/jms/Papers/foams/soap-prob.pdf'}
for n in [5,6,7,17,22,25,49,66,76]:urls['topp'+str(n)]='https://topp.openproblem.net/p'+str(n)
def fetch(item):
 k,u=item;m={'requested_url':u,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'as served; arXiv explicitly v1 where applicable','read':False}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'MathResearch/1.0'}),timeout=22) as r:
   m.update(status=r.status,final_url=r.url,headers=dict(r.headers));b=r.read(16*1024*1024+1);assert len(b)<=16*1024*1024
  m.update(size=len(b),sha256=hashlib.sha256(b).hexdigest());suffix='.pdf' if b.startswith(b'%PDF') else '.html';m['file']=k+suffix;(P/m['file']).write_bytes(b)
 except Exception as e:m.update(error=str(e),policy='no retry/bypass; no evidence of mathematical hardness')
 (P/(k+'.meta.json')).write_text(json.dumps(m,indent=2)+'\n');return k,m.get('status',m.get('error')),m.get('size')
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
 for result in ex.map(fetch,urls.items()):print(result)
