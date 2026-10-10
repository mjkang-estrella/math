"""Preseal evidence acquisition only; never run by verifier."""
import urllib.request,hashlib,json,datetime,subprocess
from pathlib import Path
S=Path(__file__).resolve().parents[2]/'sources/i93_anchored_rank_approximation_novelty_r3/external'
items=[('widths-abs.html','https://arxiv.org/abs/2111.01341'),('widths-v1.pdf','https://arxiv.org/pdf/2111.01341v1'),('uap-abs.html','https://arxiv.org/abs/math/9201220'),('uap-v1.pdf','https://arxiv.org/pdf/math/9201220v1')]
for name,url in items:
 rec=dict(name=name,url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=45) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  (S/name).write_bytes(b)
  if name.endswith('.pdf'):
   assert b.startswith(b'%PDF')
   o=subprocess.run(['pdftotext','-layout',str(S/name),'-'],capture_output=True,check=True)
   target=S/name.replace('.pdf','.txt');target.write_bytes(o.stdout);rec.update(text=target.name,text_sha256=hashlib.sha256(o.stdout).hexdigest(),extraction_returncode=o.returncode)
 except Exception as e:rec.update(error=repr(e))
 (S/(name+'.response.json')).write_text(json.dumps(rec,indent=2)+'\n');print(name,rec.get('status'),rec.get('bytes'),rec.get('error'),flush=True)
