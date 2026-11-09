from pathlib import Path
import requests,json,datetime,hashlib,subprocess
w=Path(__file__).resolve().parent
for k,u in [('1212.3641','https://arxiv.org/pdf/1212.3641'),('2401.12670','https://arxiv.org/pdf/2401.12670'),('2401.14768','https://arxiv.org/pdf/2401.14768'),('allie-publisher','https://www.tandfonline.com/doi/pdf/10.2989/16073606.2022.2053605')]:
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  r=requests.get(u,timeout=20);b=r.content;(w/'sources'/f'{k}.bin').write_bytes(b);d=dict(url=u,utc=t,status=r.status_code,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  if b.startswith(b'%PDF') and r.status_code==200:subprocess.run(['pdftotext','-layout',str(w/'sources'/f'{k}.bin'),str(w/'sources'/f'{k}.txt')],check=True)
 except Exception as e:d=dict(url=u,utc=t,error=str(e))
 (w/'sources'/f'{k}.receipt.json').write_text(json.dumps(d,indent=2));print(d,flush=True)
