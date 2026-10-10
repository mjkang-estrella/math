"""Bounded primary-source acquisition. Not part of verification."""
from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
S=Path('frontier/sources/i90_anchored_rank_approximation/external')
urls=[('well-conditioned.pdf','https://www.cs.purdue.edu/homes/pdrineas/documents/publications/Drineas_SICOMP_09.pdf'),('subset-selection.pdf','https://arxiv.org/pdf/2304.09217'),('subset-selection-abs.html','https://arxiv.org/abs/2304.09217')]
for name,url in urls:
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I90 research primary source verification'}),timeout=40) as r:
   b=r.read();meta=dict(name=name,url=url,final_url=r.url,status=r.status,headers=dict(r.headers),retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (S/name).write_bytes(b)
  if b.startswith(b'%PDF'):
   txt=S/name.replace('.pdf','.txt');p=subprocess.run(['pdftotext','-layout',str(S/name),str(txt)],capture_output=True);meta.update(text=str(txt),text_sha256=hashlib.sha256(txt.read_bytes()).hexdigest(),extraction_returncode=p.returncode)
 except Exception as e:meta=dict(name=name,url=url,error=repr(e))
 (S/(name+'.response.json')).write_text(json.dumps(meta,indent=2)+'\n');print(name,meta.get('status',meta.get('error')),flush=True)
