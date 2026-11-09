import requests,pathlib,hashlib,json,datetime,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100));os.sched_setaffinity(0,{0,1})
L=pathlib.Path(__file__).resolve().parent; (L/'sources').mkdir(exist_ok=True)
urls={ 'registry-head':'https://api.github.com/repos/OpenAI/math/commits/main', 'polygon':'https://arxiv.org/pdf/1907.08450','ppric':'https://yaakobi.net.technion.ac.il/files/2022/08/61_PPR_IT21.pdf','egz':'https://arxiv.org/pdf/1907.11236','power':'https://arxiv.org/pdf/1905.11655','forbidden':'https://arxiv.org/pdf/1905.09246','muffin':'https://arxiv.org/pdf/1907.08726','spectral':'https://arxiv.org/pdf/1907.04349'}
receipts=[]
for key,url in urls.items():
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  r=requests.get(url,timeout=25); data=r.content;p=L/'sources'/(key+('.pdf' if data.startswith(b'%PDF') else '.response'));p.write_bytes(data)
  receipts.append(dict(key=key,url=url,final_url=r.url,utc=t,status=r.status_code,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),path=str(p)))
 except Exception as e: receipts.append(dict(key=key,url=url,utc=t,error=str(e)))
 print(receipts[-1],flush=True)
 (L/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
