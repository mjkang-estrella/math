import os,resource,pathlib,requests,json,hashlib,datetime,concurrent.futures,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
o=pathlib.Path(__file__).resolve().parent/'sources';o.mkdir(exist_ok=True)
jobs={a:'https://arxiv.org/pdf/'+a for a in ['2403.16197','2403.20304','2404.18806','2404.15167','2403.17568','2403.19737','2403.09943']}
jobs.update({'openai-head':'https://api.github.com/repos/OpenAI/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'})
def fetch(k,u):
 p=o/(k+'.bin'); receipt={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(u,timeout=30);p.write_bytes(r.content);receipt.update(status=r.status_code,final_url=r.url,bytes=len(r.content),sha256=hashlib.sha256(r.content).hexdigest())
  if r.status_code==200 and r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(o/(k+'.txt'))],timeout=15,check=True)
 except Exception as e:receipt['error']=str(e)
 (o/(k+'.receipt.json')).write_text(json.dumps(receipt,indent=2));return k,receipt
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(lambda x:fetch(*x),jobs.items()):print(v,flush=True)
