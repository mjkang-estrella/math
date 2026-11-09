import requests,json,hashlib,datetime,subprocess,resource,os
from pathlib import Path
P=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(150,150));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
urls={'omega-tree.json':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/2ca21e959611edb7fe34b99383bc0bef1283fcc4?recursive=1','2512.22761.pdf':'https://arxiv.org/pdf/2512.22761','bora-choi-tang.pdf':'https://math.mit.edu/research/highschool/primes/materials/2023/Bora-Choi-Tang.pdf','2607.06515.pdf':'https://arxiv.org/pdf/2607.06515'}
r=json.loads((P/'source-receipts.json').read_text())
for n,u in urls.items():
 d={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  a=requests.get(u,timeout=40);(P/'sources'/n).write_bytes(a.content);d.update(status=a.status_code,sha256=hashlib.sha256(a.content).hexdigest(),bytes=len(a.content),final_url=a.url,file='sources/'+n)
  if a.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/n.replace('.pdf','.txt'))],check=True,timeout=25)
 except Exception as e:d['error']=str(e)
 r.append(d);print(json.dumps(d),flush=True);(P/'source-receipts.json').write_text(json.dumps(r,indent=2)+'\n')
