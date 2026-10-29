from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess
P=Path(__file__).resolve().parent
jobs=[('bernoulli-v1.pdf','https://arxiv.org/pdf/2410.13920v1'),('gu-sellke.pdf','https://arxiv.org/pdf/2605.11656v1')]
log=json.loads((P/'http.json').read_text())
for name,url in jobs:
 row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=18) as r:
   b=r.read(10*1024*1024);(P/'sources'/name).write_bytes(b);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=r.url)
  subprocess.run(['pdftotext','-layout',str(P/'sources'/name),str(P/'sources'/(name+'.txt'))],check=True)
 except Exception as e:row['error']=str(e)
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2));print(row,flush=True)
