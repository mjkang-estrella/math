from pathlib import Path
from urllib.request import urlopen,Request
from concurrent.futures import ThreadPoolExecutor
import subprocess,hashlib,json,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r204/private/primary');R.mkdir(exist_ok=True)
items=[('bruck1974','https://msp.org/pjm/1974/53-1/pjm-v53-n1-p05-p.pdf'),('bruck1975','https://www.ams.org/journals/proc/1975-053-01/S0002-9939-1975-0383164-3/S0002-9939-1975-0383164-3.pdf'),('wisnicki2012','https://arxiv.org/pdf/1203.6635v1')]
def run(item):
 name,url=item;out={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urlopen(Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=40) as h:b=h.read();out['response_url']=h.url
  if not b.startswith(b'%PDF'):raise ValueError('not PDF')
  p=R/(name+'.pdf');p.write_bytes(b);out.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  subprocess.run(['pdftotext','-layout',str(p),str(R/(name+'.txt'))],check=True,timeout=30)
  out['text_sha256']=hashlib.sha256((R/(name+'.txt')).read_bytes()).hexdigest()
 except Exception as e:out['error']=str(e)
 return out
with ThreadPoolExecutor(max_workers=3) as ex:out=list(ex.map(run,items))
(R/'access.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
