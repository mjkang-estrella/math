import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,time,datetime,urllib.request,hashlib,concurrent.futures
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic()
urls=[('365524-v1','https://arxiv.org/html/2410.20830v1'),('365524-v2','https://arxiv.org/html/2410.20830v2'),('tensor-companion','https://arxiv.org/html/2601.04514'),('tensor-companion-abs','https://arxiv.org/abs/2601.04514'),('packing-companion','https://arxiv.org/html/1512.08762'),('packing-companion-abs','https://arxiv.org/abs/1512.08762'),('pool-main','https://github.com/LeanPool/lean-pool'),('pool-projects','https://raw.githubusercontent.com/LeanPool/lean-pool/main/LeanPool/projects.yml'),('pool-candidates','https://raw.githubusercontent.com/LeanPool/lean-pool/main/candidates/README.md'),('openai-math','https://github.com/OpenAI/math')]
def fetch(v):
 n,u=v;r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired_only'}
 try:
  with urllib.request.urlopen(u,timeout=15) as f:
   b=f.read(12*1024**2);r.update(status=f.status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),final_url=f.url,file='sources/'+n+'.html');(L/r['file']).write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:rs=list(ex.map(fetch,urls))
(L/'http-receipts-follow.json').write_text(json.dumps(rs,indent=2)+'\n');print([(r['url'],r.get('status'),r.get('bytes')) for r in rs]);(L/'resource-follow.json').write_text(json.dumps({'exit':0,'wall':time.monotonic()-t,'self':list(resource.getrusage(resource.RUSAGE_SELF)),'threads_joined':True})+'\n')
