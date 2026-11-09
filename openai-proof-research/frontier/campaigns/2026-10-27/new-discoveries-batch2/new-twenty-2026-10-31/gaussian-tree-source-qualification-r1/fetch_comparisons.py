import urllib.request, json, hashlib, datetime, time, resource, subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
jobs=[('cut.pdf','https://arxiv.org/pdf/0806.0585'),('hibi.pdf','https://arxiv.org/pdf/1705.07630'),('conformal.pdf','https://arxiv.org/pdf/1206.2535'),('phylogenetic.pdf','https://arxiv.org/pdf/2006.08386')]
for name,url in jobs:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}; t=time.monotonic()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=12) as f: data=f.read(10000000); r.update(status=f.status,final_url=f.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  Path('sources',name).write_bytes(data)
  if name.endswith('.pdf'): subprocess.run(['pdftotext','-layout',str(Path('sources',name)),str(Path('sources',name).with_suffix('.txt'))],timeout=10,check=True)
 except Exception as e:r['error']=str(e)
 r['wall_seconds']=round(time.monotonic()-t,3)
 with open('fetch-receipts.jsonl','a') as f:f.write(json.dumps(r)+'\n')
 print(r,flush=True)
