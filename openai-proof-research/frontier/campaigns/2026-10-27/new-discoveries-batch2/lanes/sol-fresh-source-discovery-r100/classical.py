from pathlib import Path
import urllib.request,json,hashlib
P=Path(__file__).resolve().parent;S=P/'sources';log=[]
urls={'bcr.html':'https://arxiv.org/html/2304.05061v2','beukers.pdf':'https://swc-math.github.io/aws/2008/08BeukersSlides3.pdf','matveeva-slides.pdf':'https://amatveeva.com/wp-content/uploads/2025/10/On-the-integrality-of-some-P-recursive-sequences.pdf','yurkevich-thesis.pdf':'https://yurkevi.ch/thesis.pdf'}
for n,u in urls.items():
 try:
  r=urllib.request.urlopen(u,timeout=25);b=r.read();(S/n).write_bytes(b);log.append({'url':u,'file':'sources/'+n,'status':r.status,'sha256':hashlib.sha256(b).hexdigest()});print(n,len(b),flush=True)
 except Exception as e:log.append({'url':u,'error':str(e)});print(n,e,flush=True)
(P/'classical-http.json').write_text(json.dumps(log,indent=2))
