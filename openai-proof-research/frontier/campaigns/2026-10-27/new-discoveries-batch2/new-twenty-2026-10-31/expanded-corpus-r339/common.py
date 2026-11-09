import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,time,urllib.request,datetime,html.parser
L=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def put(n,b):
 p=(L/n).resolve();assert p.is_relative_to(L);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
def j(n,a):put(n,json.dumps(a,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
class Text(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
def fetch(url,name):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'depth':'download only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source reader'}),timeout=18) as f:b=f.read(12*1024**2);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b));put('sources/'+name,b)
  if b'%PDF'!=b[:4]:
   t=Text();t.feed(b.decode(errors='replace'));put('sources/'+name+'.txt','\n'.join(t.out))
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 j('http/'+name+'.json',r);return r
def receipt(name):j(name,{'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit_s':120,'wall_limit_s':140,'AS_bytes':6*1024**3,'wall_s':time.monotonic()-start,'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'exit':0,'limitations':'Self peak, not simultaneous group/cgroup peak; synchronous children if any reaped.'})
