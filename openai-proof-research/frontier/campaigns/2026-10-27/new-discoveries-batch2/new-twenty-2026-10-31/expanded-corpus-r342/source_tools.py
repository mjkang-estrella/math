import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,time,hashlib,sys,urllib.request,urllib.error,concurrent.futures,datetime,html.parser
P=pathlib.Path(__file__).resolve().parent
START=time.monotonic()
def write(n,x):
 f=(P/n).resolve();assert f.is_relative_to(P);f.parent.mkdir(parents=True,exist_ok=True);f.write_text(x if isinstance(x,str) else json.dumps(x,indent=2,ensure_ascii=False)+'\n')
class Text(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='img' and d.get('alt'):self.a.append(d['alt'])
 def result(self):return ' '.join(self.a)
def fetch(item):
 name,url=item;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired, not yet read'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review (public GET)'}),timeout=22) as f:
   b=f.read(12000000);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());path=(P/'sources'/name).resolve();assert path.is_relative_to(P);path.parent.mkdir(exist_ok=True);path.write_bytes(b)
   if not b.startswith(b'%PDF'):
    t=Text();t.feed(b.decode('utf-8',errors='replace'));write('sources/'+name+'.txt',t.result())
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 write('access/'+name+'.json',r);return r
if __name__=='__main__':
 label=sys.argv[1];items=json.loads(sys.argv[2]);out=[]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for r in pool.map(fetch,items):out.append(r);print(json.dumps(r),flush=True)
 u=resource.getrusage(resource.RUSAGE_SELF);write('receipts/'+label+'.json',{'true_exit':0,'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'external_wall_timeout':140,'wall_seconds':time.monotonic()-START,'self_peak_RSS_KiB':u.ru_maxrss,'self_CPU':u.ru_utime+u.ru_stime,'reaped':True,'limits':'self high water only, no cgroup/concurrent group telemetry'})
