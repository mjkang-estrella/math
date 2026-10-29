from pathlib import Path
import json,urllib.request,hashlib
P=Path(__file__).resolve().parent;log=[]
urls={'openai-kl-introduction.tex':'https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/build/01-introduction.tex','openai-kl-background.tex':'https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/build/02-background.tex'}
for n,u in urls.items():
 try:
  r=urllib.request.urlopen(u,timeout=25);b=r.read();(P/'sources'/n).write_bytes(b);log.append(dict(file='sources/'+n,url=u,status=r.status,sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:log.append(dict(url=u,error=str(e)))
(P/'more-http.json').write_text(json.dumps(log,indent=2))
