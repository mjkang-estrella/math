from pathlib import Path
import json,urllib.request,urllib.error,datetime,hashlib,subprocess
L=Path(__file__).resolve().parent
urls=[('bandwidth-successor','https://www.math.uni-hamburg.de/home/schacht/2009/bolkomr.pdf'),('automorphism','https://arxiv.org/pdf/1103.3363'),('preferential-source','https://arxiv.org/pdf/0705.4153'),('double-clustering','https://arxiv.org/pdf/0709.0511'),('sparse-ryser','https://arxiv.org/pdf/0709.3138'),('quantum-pcp','https://arxiv.org/pdf/1309.7495v1'),('bpl','https://arxiv.org/pdf/2502.08272v5'),('compression','https://arxiv.org/pdf/2410.13012v1'),('dehn','https://arxiv.org/pdf/math/9712226'),('green','https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf'),('erdos','https://www.ime.usp.br/~yoshi/resenhas/abstracts/Erdos.pdf')]
es=[];blocked=set()
for name,url in urls:
 host=urllib.parse.urlparse(url).netloc;e=dict(name=name,url=url,version='requested explicit version where present; otherwise PDF front matter',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 if host in blocked:e['status']='NOT_REQUESTED_HOST_STOP';es.append(e);continue
 try:
  with urllib.request.urlopen(url,timeout=15) as r:
   raw=r.read(12*1024*1024+1);assert len(raw)<=12*1024*1024 and raw.startswith(b'%PDF')
   p=L/'sources'/(name+'.pdf');p.write_bytes(raw);p.with_suffix('.headers').write_text(str(r.headers));e.update(status=r.status,file=str(p.relative_to(L)),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),resolved_url=r.url)
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
 except Exception as x:
  e.update(status='FETCH_FAILURE',error=str(x))
  if isinstance(x,urllib.error.HTTPError) and x.code in (403,429):blocked.add(host)
 es.append(e);print(name,e['status'],flush=True)
(L/'sources-more.json').write_text(json.dumps(es,indent=2)+'\n')
