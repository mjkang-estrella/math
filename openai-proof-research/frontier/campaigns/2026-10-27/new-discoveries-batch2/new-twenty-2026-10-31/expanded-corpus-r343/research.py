import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,hashlib,datetime,sys,time,urllib.request,concurrent.futures,html.parser,traceback
P=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def put(n,b):
 q=(P/n).resolve();assert q.is_relative_to(P);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(n,x):put(n,json.dumps(x,ensure_ascii=False,indent=2)+'\n')
class Text(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='img':self.a.append(d.get('alt',''))
  if t in ('p','div','section','h1','h2','h3','tr'):self.a.append('\n')
def fetch(pair):
 name,url=pair;rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET','read_depth':'acquired only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source research (public read-only)'}),timeout=18) as r:
   b=r.read(12000000);rec.update(status=r.status,final_url=r.url,bytes=len(b),sha256=H(b));put('sources/'+name+'.raw',b)
   if not b.startswith(b'%PDF'):
    t=Text();t.feed(b.decode('utf-8','replace'));put('sources/'+name+'.txt',''.join(t.a))
 except Exception as e:rec.update(error=str(e))
 return name,rec
started=time.monotonic();tag=str(time.time_ns());rc=0
try:
 if sys.argv[1]=='fetch':
  pairs=json.loads(sys.argv[2]);out=dict(concurrent.futures.ThreadPoolExecutor(max_workers=2).map(fetch,pairs));js('http/'+tag+'.json',out);print(json.dumps(out))
 elif sys.argv[1]=='read':
  for name,needles in json.loads(sys.argv[2]):
   q=(P/name).resolve();assert q.is_relative_to(P);t=q.read_text();print('FILE',name,'CHARS',len(t))
   if not needles:print(t)
   else:
    for needle in needles:
     start=0
     for k in range(5):
      i=t.lower().find(needle.lower(),start)
      if i<0:break
      print('WINDOW',needle,i,t[max(0,i-900):i+2600]);start=i+len(needle)
except BaseException:
 rc=1;traceback.print_exc()
finally:
 js('resources/'+tag+'.json',{'true_exit':rc,'elapsed':time.monotonic()-started,'affinity':list(os.sched_getaffinity(0)),'cpu_cap':120,'as_cap':6*1024**3,'wall_cap':140,'rusage_self':list(resource.getrusage(resource.RUSAGE_SELF)),'telemetry_limit':'self peak only; no concurrent group peak; no unreaped child processes'})
sys.exit(rc)
