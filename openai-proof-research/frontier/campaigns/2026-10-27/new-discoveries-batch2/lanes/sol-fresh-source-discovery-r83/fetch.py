from pathlib import Path
import urllib.request,urllib.error,datetime,hashlib,json
P=Path(__file__).resolve().parent
jobs=[('arvind.html','https://arxiv.org/html/2305.07301v5'),('lin.html','https://arxiv.org/html/2501.18656v1'),('hansen.pdf','https://pjm.ppu.edu/sites/default/files/papers/PJM_14(1)_2025_813_to_838.pdf'),('cp.pdf','https://arxiv.org/pdf/1510.01536'),('cameron.pdf','https://arxiv.org/pdf/2012.03789'),('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
log=[]
for name,url in jobs:
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   data=r.read(20*1024*1024);row.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(P/'sources'/name).write_bytes(data)
 except Exception as e:row['error']=str(e)
 log.append(row)
(P/'http.json').write_text(json.dumps(log,indent=2))
from bs4 import BeautifulSoup
for name in ['arvind','lin']:
 f=P/'sources'/(name+'.html')
 if f.exists():(P/'sources'/(name+'.txt')).write_text(BeautifulSoup(f.read_text(),'html.parser').get_text(' ',strip=True))
import subprocess
for name in ['cp','cameron','hansen']:
 f=P/'sources'/(name+'.pdf')
 if f.exists():subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))])
print(json.dumps(log,indent=2))
