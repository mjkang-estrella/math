"""Bounded primary retrieval; author-side only, never called by replay."""
import urllib.request,urllib.error,json,hashlib
from pathlib import Path
S=Path('frontier/sources/i144_critical_siphon_window_repulsion');D=S/'external';D.mkdir(exist_ok=True)
rows=[]
for name,url in [('boros-current','https://arxiv.org/abs/1903.03071'),('cnp-current','https://arxiv.org/abs/1010.3050'),('craciun-current','https://arxiv.org/abs/1501.02860'),('komatsu-full','https://www.sciencedirect.com/science/article/pii/S0167691125001884/pdfft?isDTMRedir=true&download=true')]:
 r=dict(url=url)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=25) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 except urllib.error.HTTPError as e:
  b=e.read();r.update(status=e.code,error=str(e),headers=dict(e.headers))
 except Exception as e:
  b=b'';r.update(status=None,error=repr(e))
 p=D/(name+'.html');p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));rows.append(r)
(S/'http-log.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['url','status','bytes']} for r in rows]))
