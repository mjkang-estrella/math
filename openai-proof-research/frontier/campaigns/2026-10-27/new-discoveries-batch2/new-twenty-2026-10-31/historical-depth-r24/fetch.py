import requests,pathlib,json,datetime,hashlib,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
D=pathlib.Path(__file__).resolve().parent;(D/'sources').mkdir(exist_ok=True); rows=[]
for name,url in [('poset','https://arxiv.org/pdf/2509.11549v1'),('capacity','https://arxiv.org/pdf/2403.10985v1'),('trees','https://arxiv.org/pdf/2609.34616v1'),('window-report','https://ems.press/journals/owr/articles/14299905'),('sun','https://oeis.org/A185150/internal')]:
 try:
  r=requests.get(url,timeout=30);p=D/'sources'/name;p.write_bytes(r.content);rows.append(dict(name=name,url=url,final_url=r.url,status=r.status_code,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content)))
  if r.status_code==200 and r.content[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],timeout=20,check=True)
 except Exception as e:rows.append(dict(name=name,url=url,error=str(e)))
 print(rows[-1],flush=True)
(D/'source-receipts.json').write_text(json.dumps(rows,indent=2))
