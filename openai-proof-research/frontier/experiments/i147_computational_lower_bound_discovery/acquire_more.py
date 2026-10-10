import json,urllib.request,hashlib,datetime,subprocess
from pathlib import Path
S=Path('frontier/sources/i147_computational_lower_bound_discovery')
items=[('ls-wsc','https://arxiv.org/pdf/2205.14003'),('pago','https://arxiv.org/pdf/2302.05426'),('bansal-sinha-v3','https://arxiv.org/pdf/2008.07003v3'),('bd-ising','https://api.repository.cam.ac.uk/server/api/core/bitstreams/0e495e74-a323-4721-89e8-1753fcaf7738/content'),('crossings','https://arxiv.org/pdf/2505.11457')]
rows=[]
for name,url in items:
 try:
  with urllib.request.urlopen(url,timeout=45) as r:b=r.read();status=r.status;final=r.url
 except Exception as e:
  rows.append(dict(url=url,error=repr(e)));continue
 p=S/'external'/f'{name}.pdf';p.write_bytes(b)
 row=dict(url=url,final_url=final,status=status,path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 if b.startswith(b'%PDF'):
  q=p.with_suffix('.txt');cp=subprocess.run(['pdftotext','-layout',str(p),str(q)],capture_output=True,text=True);row.update(text=str(q),extraction_command=['pdftotext','-layout'],extraction_exit=cp.returncode,extraction_stderr=cp.stderr)
 rows.append(row)
(S/'http-log-more.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
