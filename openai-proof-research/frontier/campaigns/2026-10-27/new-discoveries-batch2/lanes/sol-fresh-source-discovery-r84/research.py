from pathlib import Path
import urllib.request,json,hashlib,datetime,subprocess,re
P=Path(__file__).resolve().parent; R=P.parents[5]
jobs=[('bernoulli.pdf','https://iris.polito.it/retrieve/handle/11583/3006646/958922'),('wu.pdf','https://arxiv.org/pdf/2312.01819v4'),('melbourne.pdf','https://arxiv.org/pdf/2111.06997v1'),('bernoulli-abs','https://arxiv.org/abs/2410.13920'),('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-delta','https://api.github.com/repos/the-omega-institute/trureturing/compare/1b999d9fda71df7537b62327147496d64a6f66ef...e50b06adbf73bc8eaa5ae905ad0d7b0d178fe377')]
log=[]
for name,url in jobs:
 row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=18) as r:
   b=r.read(12*1024*1024);(P/'sources'/name).write_bytes(b);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=r.url)
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(P/'sources'/name),str(P/'sources'/(name+'.txt'))],check=True)
 except Exception as e:row['error']=str(e)
 log.append(row);(P/'http.json').write_text(json.dumps(log,indent=2));print(name,row.get('status',row.get('error')),flush=True)
