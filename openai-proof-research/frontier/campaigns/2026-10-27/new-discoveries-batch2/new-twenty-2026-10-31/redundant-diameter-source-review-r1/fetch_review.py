from pathlib import Path
import requests,hashlib,json,datetime,resource,os,concurrent.futures
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
jobs={'current-abs':'https://arxiv.org/abs/2403.16197','predecessor-abs':'https://arxiv.org/abs/1210.7985','predecessor-pdf':'https://arxiv.org/pdf/1210.7985','openai-head':'https://api.github.com/repos/OpenAI/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'}
def get(k,u):
 rcp={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(u,timeout=25);data=r.content;(p/(k+'.body')).write_bytes(data);rcp.update(status=r.status_code,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:rcp['error']=str(e)
 (p/(k+'.receipt.json')).write_text(json.dumps(rcp,indent=2));return k,rcp
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(lambda z:get(*z),jobs.items()): print(x,flush=True)
